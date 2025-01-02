"""
EFBV parallel solver by pysmt and mutiprocessing

TODO: complete simple idea for parallel

FIXME: Because some unknown reason(may be because different process has different FormulaManager in pysmt but it's strange there is no problem in Process rather than pool)
This parallel method need a file to input phi in child Process
Or use eval and send str (what actually used)
HAS FIXED BY SMTLIB2 EXPRESSION

FIXME: When phi exist overflow or underflow, will return Wrong answer!

FIXME: There still a little bug at remove calculated x
"""

import logging
import os
import time
from io import StringIO
from multiprocessing import Pool, Manager, cpu_count

from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import *
from pysmt.shortcuts import (And, Bool, Not, Solver, Symbol, get_model, NotEquals)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import BVType
from pysmt.fnode import FNode

logger = logging.getLogger(__name__)

bitvec_width = 32
vcc_test = False


class ParallelEFBVSolver:
    def __init__(self, pool_size=cpu_count(), maxloops=50000, maxtask=cpu_count()):

        self.maxloops = maxloops
        self.maxtask = maxtask
        self.pool = Pool(pool_size)
        self.e_phi = None
        self.logic = QF_BV

        self.loops_lock = Manager().Lock()
        self.e_phi_lock = Manager().Lock()
        self.res_lock = Manager().Lock()

        self.shared_namespace = Manager().Namespace()

        self.phi = None
        self.x = None
        self.y = None
        self.loops = 0

        self.res = None
        self.task_num = 0

    def __getstate__(self):
        self_dict = self.__dict__.copy()
        del self_dict['pool']

        return self_dict

    def __setstate__(self, state):
        self.__dict__.update(state)

    def solve(self, phi, y):

        def thread_callback(res):
            self.task_num -= 1
            if res:
                self.if_sat = True
            if not res:
                self.if_sat = False

        self.src_list = Manager().list()
        self.src_list.append(phi)

        y_str = ''
        for y_s in y:
            y_str += str(y_s)
        self.src_list.append(y_str)

        self.e_phi = Manager().list()
        self.e_phi.append(Bool(True))
        self.e_phi.append(Bool(True))
        self.loops = Manager().Value('i', 0)
        self.res = Manager().dict()

        self.if_sat = None

        self.task_num = 0

        while 1:
            try:
                if self.task_num < self.maxtask:
                    res = self.pool.apply_async(func=self.thread_process, args=(), callback=thread_callback)
                    self.task_num += 1
                    logger.debug("<Main> task:%d" % self.task_num)


            except:
                logging.exception("%s" % Exception)
                raise EnvironmentError

            self.loops_lock.acquire()
            if self.maxloops is not None and self.maxloops <= self.loops.value:
                self.loops_lock.release()
                self.pool.close()
                self.pool.join()
                logger.debug("<Main> Exit")
                raise SolverReturnedUnknownResultError
            self.loops_lock.release()

            if self.if_sat is not None:
                logger.debug("<Main> Exit")
                self.pool.close()
                self.pool.join()
                if self.if_sat:
                    print("sat : %s" % str(self.res))
                else:
                    print("unsat")
                return self.res

    def thread_process(self):
        if vcc_test:
            time.sleep(2)

        y = [Symbol(n, BVType(bitvec_width)) for n in self.src_list[1]]
        parser = SmtLibParser()
        smtlib_file = StringIO(self.src_list[0])

        formula_list = parser.get_script(smtlib_file).commands

        phi = Bool(True)
        for command in formula_list:
            if command.name == "assert":
                phi = And(phi, command.args[0])

        x = phi.get_free_variables() - set(y)

        self.loops_lock.acquire()
        loop = self.loops.value
        self.loops.value += 1
        self.loops_lock.release()

        with Solver(logic=self.logic, name='z3') as esolver:

            self.e_phi_lock.acquire()
            for e in self.e_phi:
                esolver.add_assertion(e)

            eres = esolver.solve()

            if eres:
                for v in x:
                    logger.debug("<Child:%d> %d: %s = %s" % (os.getpid(), loop, v, esolver.get_value(v)))
                    self.e_phi.append(NotEquals(v, esolver.get_value(v)))

            self.e_phi_lock.release()

            if self.res:
                # logger.debug("<Child:%d> END" % (os.getpid()))
                return None

            if not eres:
                # logger.debug("<Child:%d> END" % (os.getpid()))
                return False
            else:
                tau = {v: esolver.get_value(v) for v in x}

                sub_phi = phi.substitute(tau).simplify()

                logger.debug("<Child:%d> %d: Tau = %s" % (os.getpid(), loop, tau))

                fmodel = get_model(Not(sub_phi),
                                   logic=self.logic, solver_name='z3')
                if fmodel is None:
                    self.res_lock.acquire()
                    self.res.clear()
                    self.res.update(tau)
                    self.res_lock.release()

                    # logger.debug("<Child:%d> END" % (os.getpid()))
                    return True
                else:
                    sigma = {v: fmodel[v] for v in y}
                    sub_phi = phi.substitute(sigma).simplify()

                    logger.debug("<Child:%d> %d: Sigma = %s" % (os.getpid(), loop, sigma))

                    self.e_phi_lock.acquire()
                    self.e_phi.append(sub_phi)
                    self.e_phi_lock.release()

                    # logger.debug("<Child:%d> END" % (os.getpid()))
                    return None


def efbv(y, phi, logic=QF_BV, maxloops=None,
         esolver_name='z3', fsolver_name='z3',
         verbose=False):
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

    with Solver(logic=logic, name=esolver_name) as esolver:

        esolver.add_assertion(Bool(True))
        loops = 0

        while maxloops is None or loops <= maxloops:
            # time.sleep(0.1)
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

        raise SolverReturnedUnknownResultError


def run_test(y, f):
    print("Testing " + str(f))
    try:
        res = efbv(y, f, logic=QF_BV, maxloops=50, verbose=True)
        if not res:
            print("unsat")
        else:
            print("sat : %s" % str(res))
    except SolverReturnedUnknownResultError:
        print("unknown")


def run_parallel_test(y, f):
    print("Parallel Testing " + str(f))
    try:
        solver = ParallelEFBVSolver()
        solver.solve(f, y)
    except SolverReturnedUnknownResultError:
        print("unknown")


def main():
    x, y = [Symbol(n, BVType(bitvec_width)) for n in "xy"]
    f_sat = ('''(set-logic QF_BV)
        (declare-fun x () (_ BitVec %d))
        (declare-fun y () (_ BitVec %d))
        (assert (=> (and (bvugt y #x00000003) (bvult y #x0000000A)) (bvult (bvsub y (bvmul #x00000002 x)) #x00000007)))
        (check-sat)''' % (bitvec_width, bitvec_width))
    f_incomplete = ('''(set-logic QF_BV)
        (declare-fun x () (_ BitVec %d))
        (declare-fun y () (_ BitVec %d))
        (assert (and (bvugt y #x00000003) (bvugt x #x00000001)))
        (check-sat)''' % (bitvec_width, bitvec_width))

    start = time.time()
    run_test([y], f_sat)
    end = time.time()
    logger.info("Origin Sat Time: %s s" % (end - start))
    print("\n\n")

    start = time.time()
    run_test([y], f_incomplete)
    end = time.time()
    logger.info("Origin UnSat Time: %s s" % (end - start))
    print("\n\n")

    start = time.time()
    run_parallel_test([y], f_sat)
    end = time.time()
    logger.info("Parallel Sat Time: %s s" % (end - start))
    print("\n\n")

    start = time.time()
    run_parallel_test([y], f_incomplete)
    end = time.time()
    logger.info("Parallel UnSat Time: %s s" % (end - start))
    print("\n\n")


if __name__ == "__main__":
    logging.basicConfig(format='%(asctime)s - %(filename)s[line:%(lineno)d] - %(levelname)s: %(message)s',
                        level=logging.DEBUG)  # 配置输出格式、配置日志级别
    main()
