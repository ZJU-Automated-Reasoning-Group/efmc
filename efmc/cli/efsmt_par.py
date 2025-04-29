"""
FIXME: this file is not used for now.

EFBV parallel solver by pysmt and mutiprocessing

Improved implementation with:
- Better synchronization between processes
- Fixed issue with calculated x removal
- Improved error handling for overflow/underflow
- Enhanced performance with early termination
"""

import logging
import os
import time
import signal
import sys
from io import StringIO
from multiprocessing import Pool, Manager, cpu_count, TimeoutError

from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import *
from pysmt.shortcuts import (And, Bool, Not, Solver, Symbol, get_model, NotEquals, Equals)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BVType
from pysmt.fnode import FNode

logger = logging.getLogger(__name__)

bitvec_width = 32
vcc_test = False

# Add timeout for solver operations
SOLVER_TIMEOUT = 30  # seconds

from efmc.engines.ef.efsmt.efsmt_parser import EFSMTParser, ParserError
from pysmt.oracles import get_logic
from pysmt.shortcuts import get_env
from pysmt.smtlib.parser import SmtLibParser


class ParallelEFBVSolver:
    def __init__(self, pool_size=cpu_count(), maxloops=50000, maxtask=cpu_count(), timeout=SOLVER_TIMEOUT):
        self.maxloops = maxloops
        self.maxtask = maxtask
        self.pool = Pool(pool_size)
        active_pools.append(self.pool)  # Register pool for cleanup
        self.e_phi = None
        self.logic = QF_BV
        self.timeout = timeout

        # Improved synchronization with Manager
        manager = Manager()
        self.loops_lock = manager.Lock()
        self.e_phi_lock = manager.Lock()
        self.res_lock = manager.Lock()
        self.task_lock = manager.Lock()

        # Track processed values to avoid redundant calculations
        self.processed_values = manager.list()

        self.phi = None
        self.x = None
        self.y = None
        self.loops = 0

        self.res = None
        self.task_num = 0
        self.terminate_flag = manager.Value('b', False)
        self.parser = EFSMTParser()

    def _convert_z3_to_pysmt(self, z3_expr):
        """Convert Z3 expression to pySMT format"""
        # Convert to SMT-LIB string and parse with pySMT
        smt2_str = z3_expr.sexpr()
        parser = SmtLibParser()
        script = parser.get_script(StringIO(smt2_str))
        return script.get_last_formula()

    def solve(self, phi, y):
        def thread_callback(res):
            with self.task_lock:
                self.task_num -= 1
                if res is True:
                    self.terminate_flag.value = True
                    self.if_sat = True
                elif res is False:
                    self.if_sat = False

        # Parse with EFSMTParser
        self.parser.set_logic('BV')
        z3_exists_vars, z3_forall_vars, z3_formula = self.parser.parse_smt2_string(phi)

        # Convert to pySMT format
        formula = self._convert_z3_to_pysmt(z3_formula)
        forall_vars = [self._convert_z3_to_pysmt(v) for v in z3_forall_vars]
        exists_vars = [self._convert_z3_to_pysmt(v) for v in z3_exists_vars]

        self.src_list = Manager().list()
        self.src_list.append(str(formula))

        y_str = ''
        for y_s in forall_vars:
            y_str += str(y_s)
        self.src_list.append(y_str)

        self.e_phi = Manager().list()
        self.e_phi.append(Bool(True))
        self.e_phi.append(Bool(True))
        self.loops = Manager().Value('i', 0)
        self.res = Manager().dict()

        self.if_sat = None
        self.task_num = 0

        # Add timeout handling
        start_time = time.time()

        while not self.terminate_flag.value:
            # Check timeout
            if self.timeout and time.time() - start_time > self.timeout:
                logger.warning("Solver timeout reached after %s seconds", self.timeout)
                self.pool.close()
                self.pool.join()
                raise SolverReturnedUnknownResultError("Timeout")

            # Check max loops
            with self.loops_lock:
                if self.maxloops is not None and self.maxloops <= self.loops.value:
                    self.pool.close()
                    self.pool.join()
                    logger.debug("<Main> Exit due to max loops")
                    raise SolverReturnedUnknownResultError("Maximum iterations reached")

            # Check if we have a result
            if self.if_sat is not None:
                logger.debug("<Main> Exit with result: %s", "sat" if self.if_sat else "unsat")
                self.pool.close()
                self.pool.join()
                if self.if_sat:
                    print("sat : %s" % str(self.res))
                else:
                    print("unsat")
                return self.res

            # Spawn new tasks if needed
            try:
                with self.task_lock:
                    if self.task_num < self.maxtask and not self.terminate_flag.value:
                        res = self.pool.apply_async(func=self.thread_process, args=(), callback=thread_callback)
                        self.task_num += 1
                        logger.debug("<Main> task:%d", self.task_num)
            except Exception as e:
                logging.exception("Error spawning task: %s", str(e))
                raise EnvironmentError(f"Failed to spawn task: {str(e)}")

            # Add sleep to prevent CPU hogging
            time.sleep(0.01)

    def thread_process(self):
        if vcc_test:
            time.sleep(2)

        # Check if we should terminate early
        if self.terminate_flag.value:
            return None

        try:
            # Parse using stored formula
            y = [Symbol(n, BVType(bitvec_width)) for n in self.src_list[1]]
            parser = SmtLibParser()
            smtlib_file = StringIO(self.src_list[0])
            formula_list = parser.get_script(smtlib_file).commands

            phi = Bool(True)
            for command in formula_list:
                if command.name == "assert":
                    phi = And(phi, command.args[0])

            x = phi.get_free_variables() - set(y)

            with self.loops_lock:
                loop = self.loops.value
                self.loops.value += 1

            # Early termination check
            if self.terminate_flag.value:
                return None

            with Solver(logic=self.logic, name='z3') as esolver:
                # Add overflow/underflow detection
                try:
                    with self.e_phi_lock:
                        for e in self.e_phi:
                            esolver.add_assertion(e)

                        # Check for already processed values to avoid redundant work
                        for val in self.processed_values:
                            for v, value in val.items():
                                if v in x:
                                    esolver.add_assertion(NotEquals(v, value))

                        eres = esolver.solve()

                        if eres:
                            # Store the current assignment to avoid recalculating
                            current_assignment = {}
                            for v in x:
                                value = esolver.get_value(v)
                                current_assignment[v] = value
                                logger.debug("<Child:%d> %d: %s = %s", os.getpid(), loop, v, value)

                            # Add to processed values
                            self.processed_values.append(current_assignment)

                            # Add constraints to avoid this assignment in future
                            for v, value in current_assignment.items():
                                self.e_phi.append(NotEquals(v, value))
                except Exception as e:
                    logger.error("Solver error (possible overflow/underflow): %s", str(e))
                    return None

                # Release lock after solving

                # Check if another process found a solution
                if self.terminate_flag.value or self.res:
                    return None

                if not eres:
                    return False
                else:
                    tau = {v: esolver.get_value(v) for v in x}

                    # Check for overflow/underflow in substitution
                    try:
                        sub_phi = phi.substitute(tau).simplify()
                    except Exception as e:
                        logger.error("Substitution error (possible overflow/underflow): %s", str(e))
                        # Skip this assignment and try another
                        return None

                    logger.debug("<Child:%d> %d: Tau = %s", os.getpid(), loop, tau)

                    try:
                        fmodel = get_model(Not(sub_phi), logic=self.logic, solver_name='z3')
                        if fmodel is None:
                            with self.res_lock:
                                if not self.terminate_flag.value:
                                    self.terminate_flag.value = True
                                    self.res.clear()
                                    self.res.update(tau)
                            return True
                        else:
                            sigma = {v: fmodel[v] for v in y}
                            sub_phi = phi.substitute(sigma).simplify()
                            logger.debug("<Child:%d> %d: Sigma = %s", os.getpid(), loop, sigma)

                            with self.e_phi_lock:
                                self.e_phi.append(sub_phi)
                            return None
                    except Exception as e:
                        logger.error("Model generation error: %s", str(e))
                        return None

        except Exception as e:
            logger.error("Thread process error: %s", str(e))
            return None


def efbv(y, phi, logic=QF_BV, maxloops=None,
         esolver_name='z3', fsolver_name='z3',
         verbose=False, timeout=None):  # Add timeout parameter
    """Solves exists x. forall y. phi(x, y)"""

    parser = SmtLibParser()
    smtlib_file = StringIO(phi)

    formula_list = parser.get_script(smtlib_file).commands

    phi = Bool(True)
    for command in formula_list:
        if command.name == "assert":
            phi = And(phi, command.args[0])

    y = set(y)
    x = phi.get_free_variables() - y

    # Add timeout handling
    start_time = time.time()

    with Solver(logic=logic, name=esolver_name) as esolver:
        esolver.add_assertion(Bool(True))
        loops = 0

        while maxloops is None or loops <= maxloops:
            # Check timeout if specified
            if timeout and time.time() - start_time > timeout:
                logger.warning("Solver timeout reached after %s seconds", timeout)
                raise SolverReturnedUnknownResultError("Timeout")

            if vcc_test:
                time.sleep(2)

            loops += 1

            eres = esolver.solve()
            if not eres:
                return False
            else:
                tau = {v: esolver.get_value(v) for v in x}
                sub_phi = phi.substitute(tau).simplify()
                if verbose: print("%d: Tau = %s" % (loops, tau))
                fmodel = get_model(Not(sub_phi),
                                   logic=logic, solver_name=fsolver_name)
                if fmodel is None:
                    return tau
                else:
                    sigma = {v: fmodel[v] for v in y}
                    sub_phi = phi.substitute(sigma).simplify()
                    if verbose: print("%d: Sigma = %s" % (loops, sigma))
                    esolver.add_assertion(sub_phi)

        raise SolverReturnedUnknownResultError("Maximum iterations reached")


def run_test(y, f, timeout=SOLVER_TIMEOUT):
    print("Testing " + str(f))
    try:
        res = efbv(y, f, logic=QF_BV, maxloops=50, verbose=True, timeout=timeout)
        if not res:
            print("unsat")
        else:
            print("sat : %s" % str(res))
    except SolverReturnedUnknownResultError as e:
        print(f"unknown: {str(e)}")
    except Exception as e:
        print(f"error: {str(e)}")


def run_parallel_test(timeout=SOLVER_TIMEOUT):
    fml = """
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun x3 () (_ BitVec 8))
(assert
    (forall ((y1 (_ BitVec 8)) (y2 (_ BitVec 8)))
        (=> (and (bvult y1 y2)
                 (bvugt y2 x1))
            (or (= (bvand x1 y1) x2)
                (and (bvule (bvadd x2 y2) x3)
                     (= (bvmul y1 x3) y2))))))"""

    parser = EFSMTParser()
    parser.set_logic('BV')
    exists_vars, forall_vars, formula = parser.parse_smt2_string(fml)

    solver = None
    try:
        solver = ParallelEFBVSolver(timeout=timeout)
        result = solver.solve(fml, forall_vars)
        return result
    except KeyboardInterrupt:
        print("\nTest interrupted by user")
        if solver and hasattr(solver, 'pool'):
            solver.pool.terminate()
            solver.pool.join()
    except SolverReturnedUnknownResultError as e:
        print(f"unknown: {str(e)}")
    except Exception as e:
        print(f"error: {str(e)}")
    finally:
        # Ensure pool is cleaned up
        if solver and hasattr(solver, 'pool'):
            try:
                solver.pool.terminate()
                solver.pool.join()
            except:
                pass


# Add signal handler for graceful termination
def signal_handler(sig, frame):
    print("\nCaught Ctrl+C, terminating gracefully...")
    # Force terminate all pools
    for p in active_pools:
        if p:
            p.terminate()
            p.join()
    sys.exit(0)


# Keep track of active pools for cleanup
active_pools = []

# Register signal handler
signal.signal(signal.SIGINT, signal_handler)

if __name__ == "__main__":
    logging.basicConfig(format='%(asctime)s - %(filename)s[line:%(lineno)d] - %(levelname)s: %(message)s',
                        level=logging.DEBUG)  # 配置输出格式、配置日志级别
    run_parallel_test()
