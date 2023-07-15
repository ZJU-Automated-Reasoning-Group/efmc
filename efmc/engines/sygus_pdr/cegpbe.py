# since passing the transition function is relatively slow
# we use PBE
# but we have to do in cex-guided way
# 1. simulation to next frame

from pysmt.shortcuts import Not, And, Implies, EqualsOrIff
from pysmt.shortcuts import Solver
from datetime import datetime

import subprocess

import efmc.engines.sygus_pdr.sygus as sygus_if2
from efmc.engines.sygus_pdr.getfunc import FuncParser
from efmc.engines.ef.efsmt.efsmt_config import cvc5_exec

Config_use_init_data = True
Config_cvc5_path = cvc5_exec
Config_debug_dump = True
Config_cvc5_time_out = 30


class Sim:
    def __init__(self, solver, T, prev_state, primal_vars, prime_vars, primal_map, constr=None):
        self.solver = solver
        self.prev_state = prev_state
        self.constr = constr
        self.T = T
        self.prime_vars = prime_vars
        self.primal_vars = primal_vars
        self.primal_map = primal_map
        self.to_block_prime_state_list = []  # list of list of (v, val)

        # sanity check: no prime vars
        for v, _ in self.prev_state:
            assert (v not in self.prime_vars)
            assert (v in self.primal_vars)
            # assert (not v.symbol_name().endswith('_prime'))

        if self.constr is None:
            self.constr = [EqualsOrIff(v, val) for v, val in self.prev_state]
        elif not isinstance(self.constr, list):
            self.constr = [self.constr]  # if it is just a single expression

        assert (isinstance(self.constr, list))
        assert (len(self.constr) > 0)

    def PostState(self, remove_vars=[], keep_vars=None):
        # s /\ T == sat ?  get v prime
        sat = self.solver.solve(self.constr + [self.T] + \
                                [Not(And([EqualsOrIff(vp, val) for vp, val in post_state_assign])) \
                                 for post_state_assign in self.to_block_prime_state_list])

        if len(self.to_block_prime_state_list) == 0:
            assert sat

        if not sat:  # could be possible if combined with BlockPostState
            return []
        # assert (sat) # we should start from

        retL = []
        for v, val in self.solver.get_model():
            if v not in self.prime_vars:
                continue

            v_primal_vars = self.primal_map[v]
            if v_primal_vars in remove_vars:
                continue
            if isinstance(keep_vars, list) and len(keep_vars) > 0 and v_primal_vars not in keep_vars:
                continue
            retL.append((v, val))

        assert (len(retL) > 0)  # not empty
        return retL  # note : this is    (v', val)    v'   prime var

    def BlockPostState(self, sat_instance_of_post_state):
        self.to_block_prime_state_list.append(sat_instance_of_post_state)


#
# F_idx_minus2 /\ T => inv
# F_idx_minus2 => inv
# inv => itp ? (make it stronger) no
#

class CexGuidedPBE:
    def __init__(self,
                 primal_vars, prime_vars, primal_map, prime_map,
                 T, F_idx_minus2, Init,
                 inv_var_set, facts_on_inv_vars, cexs_on_inv_vars,
                 sorted_inv_var_set, sorted_allvars, sorted_prime_vars,
                 op_obj):

        # itp is used for opextract
        # ctg is used for vars
        # itp, ctg, facts, blocked_cexs): # allvars, prime_vars
        if len(facts_on_inv_vars) == 0:
            print('[SyGuS] Warning: No facts!')
        assert (len(cexs_on_inv_vars) > 0)
        # otherwise no need to start such synthesis ?
        # blocked_cexs can be loosen, from T, F_idx_minus2

        self.primal_vars, self.prime_vars, self.primal_map, self.prime_map, \
            self.T, self.F_idx_minus2, self.Init, \
            self.inv_var_set, self.facts_on_inv_vars, self.cexs_on_inv_vars, \
            self.sorted_inv_var_set, self.sorted_allvars, self.sorted_prime_vars, \
            self.op_obj = \
            primal_vars, prime_vars, primal_map, prime_map, \
                T, F_idx_minus2, Init, \
                inv_var_set, facts_on_inv_vars, cexs_on_inv_vars, \
                sorted_inv_var_set, sorted_allvars, sorted_prime_vars, \
                op_obj

        self.inv_var_set_prime = set([prime_map[v] for v in self.inv_var_set])

        self.solver = Solver()  # name = 'btor'

    # synthesize F-2 ==> INV
    # synthesize F-2 /\ T ==> INV

    def syn_one_instance(self, new_facts, timeout=None):  # add init config

        sygus_if2.Config_use_trans = True
        sygus_if2.Config_use_init = True
        sygus_if2.Config_use_facts = len(self.facts_on_inv_vars + new_facts) != 0

        sygus_query = sygus_if2.SyGusQueryGen(
            primal_vars=self.primal_vars, prime_vars=self.prime_vars,
            T=self.T, F_idx_minus2=self.F_idx_minus2, Init=self.Init,
            inv_var_set=self.inv_var_set, facts_on_inv_vars=self.facts_on_inv_vars + new_facts,
            cexs_on_inv_vars=self.cexs_on_inv_vars,
            sorted_inv_var_set=self.sorted_inv_var_set, sorted_allvars=self.sorted_allvars,
            sorted_prime_vars=self.sorted_prime_vars,
            op_obj=self.op_obj)

        suffix = ''
        if Config_debug_dump:
            now = datetime.now()
            suffix = now.strftime("%Y-%m-%d-%H-%M-%S")
        query_fn = 'sygus_queries/q' + suffix + '.sygus'
        result_fn = 'sygus_queries/q' + suffix + '-a.sygus'

        sygus_query.gen_sygus_query(query_fn)

        try:
            with open(result_fn, "w") as outf:  # TIMEOUT
                subprocess.call([Config_cvc5_path, '--lang=sygus2', query_fn], stdout=outf,
                                timeout=Config_cvc5_time_out)
        except subprocess.TimeoutExpired:
            print('[CVC5] reports time out.')
            return None

        with open(result_fn) as fin:
            result = fin.readline()
            if 'unsat' in result:
                func = fin.read()
                itp = FuncParser(func, self.sorted_inv_var_set)
                return itp
        return None

    def cex_to_current_next_var(self, cex):
        cur_all_var = []
        cur = []
        nxt = []
        for v, val in cex:
            if v in self.primal_vars:
                cur_all_var.append((v, val))
                if v in self.inv_var_set:
                    cur.append((v, val))
            elif v in self.inv_var_set_prime:
                nxt.append((v, val))
        return cur_all_var, cur, nxt

    def syn_lemma_F_T_implies_lemma_prime(self, fidx=None, lidx=None, itp=None, frame_dump=None):
        if Config_debug_dump:
            now = datetime.now()
            summary_fn = 'sygus_queries/q' + now.strftime("%Y-%m-%d-%H-%M-%S") + '-summary.txt'
            with open(summary_fn, 'w') as fout:
                fout.write('Fidx: ' + str(fidx) + ' to fidx+1\n')
                fout.write('Lidx: ' + str(lidx) + '\n')
                fout.write('Itp: ' + itp.serialize() if itp else 'None' + '\n')
                fout.write('\n--------------------------\n')
                fout.write(str(frame_dump))

        itp = self.syn_one_instance(new_facts=[])
        print('  [SyGuS] get itp :', itp.serialize() if itp is not None else 'None')
        return itp

    def syn_loop(self, fidx=None, lidx=None, itp=None, frame_dump=None):
        if Config_debug_dump:
            now = datetime.now()
            summary_fn = 'sygus_queries/q' + now.strftime("%Y-%m-%d-%H-%M-%S") + '-summary.txt'
            with open(summary_fn, 'w') as fout:
                fout.write('Fidx: ' + str(fidx) + '\n')
                fout.write('Lidx: ' + str(lidx) + '\n')
                fout.write('Itp: ' + itp.serialize() if itp else 'None' + '\n')
                fout.write('--------------------------\n')
                fout.write(str(frame_dump))

        new_facts = []

        while True:
            itp = self.syn_one_instance(new_facts)
            print('[CexGuidedPBE] get sygus result:', itp.serialize() if itp is not None else 'None')
            if itp is None:
                return None
                # sygus failed : unknown

            # if
            m1 = self.solve(Not(Implies(And(self.F_idx_minus2), itp)), keep_vars=self.inv_var_set)
            if m1 is not None:
                assert (len(m1) > 0)  # other wise , we are dropping too many variables, cannot be
                assert (m1 not in new_facts)
                # TODO: FIXME
                # new cex
                new_facts.append(dict(m1))
                continue

            itp_prime_var = itp.substitute(self.prime_map)
            m2 = self.solve(Not(Implies(And(self.F_idx_minus2 + [self.T]), itp_prime_var)),
                            keep_vars=self.inv_var_set_prime)
            if m2 is not None:
                assert (len(m2) > 0)  # other wise , we are dropping too many variables, cannot be
                assert (m2 not in new_facts)
                # replace to
                new_facts.append({self.primal_map[v]: val for v, val in m2})
                continue

            assert (m1 is None and m2 is None)
            break  # we are done

        return itp
        # TODO: FIXME
        # new cex

        # F_idx_minus2 /\ T => inv
        # F_idx_minus2 => inv

    def solve(self, formula, keep_vars=None):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        # you should know to drop variables here
        # plus tenary simulation ? ast-walker
        if self.solver.solve([formula]):
            # you may need to enumerate keep_vars and use get_value....
            retL = []
            for v, val in self.solver.get_model():
                if (isinstance(keep_vars, list) or isinstance(keep_vars, set)) and len(
                        keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v, val))
                # retL.append(EqualsOrIff(v, val))
            assert (len(retL) > 0)  # otherwise we are removing too many variables!
            # return And(retL)
            return retL
        return None
