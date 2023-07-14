"""
PDR guided by SyGuS (from Hongce Zhang)
"""
from pysmt.fnode import FNode
from pysmt.shortcuts import Not, And, Or, Implies, EqualsOrIff
from pysmt.shortcuts import Solver
# from pysmt.typing import BOOL, BVType
from pysmt.shortcuts import Interpolator, simplify
from pysmt.logics import QF_BV
# Type annotation
from typing import Sequence, Callable, Mapping, Tuple

from efmc.engines.sygus_pdr.utilfunc import _get_var, _get_cubes_with_more_var  # , _get_cubes_with_fewer_var
from efmc.engines.sygus_pdr.cegpbe import CexGuidedPBE
from efmc.engines.sygus_pdr.opextract import OpExtractor
from efmc.engines.sygus_pdr.sts import TransitionSystem, BaseAddrCnt, TwoCnt, TwoCntNoload

import heapq

# ----------- Basic Parameters -------------------
Config_Max_Frame = 10000000
Config_use_itp_in_pushing = False
Config_analyze_use_itp_in_pushing = True
Config_debug = True
Config_debug_print = True
Config_simplify_itp = True
Config_rm_cex_in_prev = True
Config_use_sygus = True
# ----------- Heuristics -------------------
Config_enhance_giveup_threshold = (2, 3)  # (8,10)
Config_cex_invalid_itp_guess_threshold = (4, 5)  # (18, 20)
Config_try_drop_cex = (5, 5)  # (30, 50)  # after 30 frames, per 50
# ----------- NEEDS EXPERIMENTS -------------------
Config_use_fact_in_sygus = False
Config_strengthen_effort_for_prop = 1e4  # almost infinity (should make it 1000?)


def pause():
    if Config_debug:
        input()


def debug(*l, **k):
    if Config_debug_print:
        print(*l, **k)


# ----------- AUX FUNCTIONS -------------------
def _cube2prop(cube):
    return Not(And([EqualsOrIff(v, val) for v, val in cube]))


def print_cube(c):
    return '(' + (' && '.join([v.symbol_name() + ' = ' + str(val) for v, val in c])) + ')'


# ----------- AUX CLASSES -------------------

class Lemma(object):
    @classmethod
    def _canonicalize_cex(cls, cex):
        """cex to a hashable thing"""
        cex_str = [(v.symbol_name(), val) for v, val in cex]
        return tuple(sorted(cex_str, key=lambda x: x[0]))

    def __init__(self, expr: FNode, cex, origin: str):
        # cex should be a set
        # cex: Sequence[Sequence[Tuple(FNode, FNode)]]
        assert (isinstance(cex, list))
        self.expr = expr
        self.cex = cex
        self.origin = origin
        self.pushed = False
        # statistics
        self.itp_push_fail = (0, 0)
        self.itp_enhance_fail = (0, 0)

    def copy(self):
        """return one that has no stat, no pushed"""
        return Lemma(expr=self.expr, cex=self.cex, origin=self.origin)

    def stats_push_fail(self, failed: bool):
        self.itp_push_fail = (self.itp_push_fail[0] + (1 if failed else 0), self.itp_push_fail[1] + 1)

    def stats_sygus_fail(self, failed: bool):
        self.itp_enhance_fail = (self.itp_enhance_fail[0] + (1 if failed else 0), self.itp_enhance_fail[1] + 1)

    def direct_push(self) -> "Lemma":  # -> Lemma:
        self.pushed = True
        ret = Lemma(expr=self.expr, cex=self.cex, origin=self.origin)
        self.stats_push_fail(False)
        ret.itp_push_fail = self.itp_push_fail
        ret.itp_enhance_fail = self.itp_enhance_fail
        return ret

    def subsume_by_frame(self, fidx: int, pdr: 'PDR') -> bool:
        for c in self.cex:
            if not pdr.is_valid(Implies(pdr.frame_prop(fidx), _cube2prop(c))):
                return False
        return True

    # *** END OF subsume_by_frame ***
    def try_itp_push(self, fc: 'FrameCache', src_fidx: int, pdr: 'PDR', remove_vars=[], keep_vars=None):
        assert len(self.cex) == 1
        blockable = pdr.try_recursive_block(cube=self.cex[0], idx=src_fidx + 1, cex_origin=self.origin,
                                            frame_cache=fc, remove_vars=remove_vars, keep_vars=keep_vars)
        if blockable:
            assert len(fc.frames[src_fidx + 1]) == 1, 'expect 1 interpolant on fc!'
            self.stats_push_fail(False)
            fc.frames[src_fidx + 1][0].itp_push_fail = self.itp_push_fail
            return False, fc.frames[src_fidx + 1][0]
        return True, None

    # *** END OF try_itp_push ***
    def try_strengthen(self, fc: 'FrameCache', bnd: int, src_fidx: int, pdr: 'PDR', prev_ex, remove_vars=[],
                       keep_vars=None):
        # first try to strengthen itself
        # then try to strengthen the extra ones on fc
        # returns 'prop_succ, all_succ, rmBnd, unblockable_cube'
        assert prev_ex is not None
        while prev_ex is not None:
            blockable = pdr.try_recursive_block(cube=prev_ex, idx=src_fidx, cex_origin='push_lemma',
                                                frame_cache=fc, remove_vars=remove_vars, keep_vars=keep_vars)
            if not blockable:
                self.stats_push_fail(True)
                return False, False, bnd, prev_ex
            # get next prev_ex
            prev_ex, _, _ = \
                pdr.solveTrans(prevF=pdr.frame_prop_list(src_fidx) + fc.frame_prop_list(src_fidx),
                               T=pdr.system.trans, prop=self.expr, variables=pdr.system.variables,
                               init=None, remove_vars=remove_vars, keep_vars=keep_vars,
                               findItp=False, get_post_state=False)
            bnd -= 1
            if bnd < 0:
                self.stats_push_fail(True)
                return False, False, bnd, prev_ex  # bound limit reached
        # add its direct push to fc next level
        # prev_ex is None from this point
        fc._add_lemma(lemma=self.direct_push(), fidx=src_fidx + 1)
        # prop_succ = True from this point
        # try block all lemmas on the current frame
        for l in fc.frames.get(src_fidx, []):
            # try push once to get prev_cex
            prev_ex, _, _ = \
                pdr.solveTrans(prevF=pdr.frame_prop_list(src_fidx) + fc.frame_prop_list(src_fidx),
                               T=pdr.system.trans, prop=self.expr, variables=pdr.system.variables,
                               init=None, remove_vars=remove_vars, keep_vars=keep_vars,
                               findItp=False, get_post_state=False)
            if prev_ex is None:
                continue

            prop_succ, all_succ, rmBnd, unblockable_cube = \
                l.try_strengthen(fc=fc, bnd=bnd, src_fidx=src_fidx, pdr=pdr, prev_ex=prev_ex,
                                 remove_vars=remove_vars, keep_vars=keep_vars)
            bnd = rmBnd
            if bnd < 0:
                return True, False, bnd, None
            # if it is pushable, it has been pushed to the next frame
            if not (all_succ or prop_succ):
                assert (unblockable_cube is not None)
                return True, False, bnd, unblockable_cube
            # copy past
        # all pushable
        return True, True, bnd, None

    # *** END OF try_strengthen ***

    # ----------- !!! PUSH LEMMA !!! -------------------
    def _try_sygus_repair(self, fidx: int, lemmaIdx: int, post_ex, new_itp, pdr: 'PDR', remove_vars, keep_vars):
        # TODO: better var set determination
        opextract = OpExtractor()  # work on itp
        opextract.walk(self.expr)
        opextract.walk(new_itp.expr)
        lemma_var_set = opextract.Symbols
        post_ex_var_set = _get_var(post_ex)  # this is necessary
        inv_var_set = lemma_var_set.union(post_ex_var_set)
        sorted_inv_var_set = sorted(list(inv_var_set), key=lambda x: x.symbol_name())
        blocked_cexs = [dict(c) for c in self.cex]  # fidx+1 is fewer cex

        # it is a question on whether using fact actually ....
        facts = pdr.unblockable_fact.get(fidx + 1, [])  # facts should be more facts
        facts_on_inv_vars = _get_cubes_with_more_var(facts, inv_var_set)  # and will shrink var
        sorted_allvars = sorted(pdr.system.variables, key=lambda x: x.symbol_name())
        sorted_prime_vars = sorted(pdr.system.prime_variables, key=lambda x: x.symbol_name())

        pdr.dump_frames()
        print('  [push_lemma F%d] Invoke SyGuS Now:' % fidx)
        print('----------------\nvarset:\n', inv_var_set)
        print('----------------\ncex:\n', blocked_cexs)
        print('----------------\nfacts:\n', facts_on_inv_vars)
        assert not (len(blocked_cexs) == 0 and len(facts_on_inv_vars) == 0)

        # this is very important ? to remove the old one ? so it is a replacement
        cex_guided_pbe = CexGuidedPBE(
            primal_vars=pdr.system.variables,
            prime_vars=pdr.system.prime_variables,
            primal_map=pdr.primal_map,  # next_v --> v
            prime_map=pdr.prime_map,  # v --> next_v
            T=pdr.system.trans,
            F_idx_minus2=pdr.frame_prop_select(fidx=fidx, selector=lambda lidx: lidx != lemmaIdx),
            Init=pdr.system.init,  # IMPROVEMENT: Use init
            inv_var_set=inv_var_set,  # we can change this if necessary
            facts_on_inv_vars=facts_on_inv_vars if Config_use_fact_in_sygus else [],
            cexs_on_inv_vars=blocked_cexs,
            sorted_inv_var_set=sorted_inv_var_set,
            sorted_allvars=sorted_allvars,
            sorted_prime_vars=sorted_prime_vars,
            op_obj=opextract)

        # lemma /\ F /\ T => lemma'
        itp = cex_guided_pbe.syn_lemma_F_T_implies_lemma_prime(
            fidx=fidx, lidx=lemmaIdx, itp=self.expr,
            frame_dump=pdr.dump_frames(toStr=True))

        if itp is None:
            print('  [push_lemma F%d] Repair lemma l%d failed: ' % (fidx, lemmaIdx))
            self.stats_sygus_fail(True)
            return None

        itp_prime_var = itp.substitute(cex_guided_pbe.prime_map)
        assert (pdr.is_valid(Implies(pdr.system.init, itp)))
        assert (pdr.is_valid(Implies(And(pdr.frame_prop_list(fidx) + [pdr.system.trans, itp]), itp_prime_var)))
        ret = Lemma(expr=itp, cex=self.cex, origin=self.origin)
        # get statistics right
        self.stats_sygus_fail(False)
        return ret

    # *** END OF _try_sygus_repair ***

    def serialize(self) -> str:
        return self.expr.serialize()

    def dump_expr(self) -> str:
        return (
                ('P' if self.pushed else ' ') +
                (' | ' + self.expr.serialize()) +
                (' | ' + self.origin) +
                (' | ' + str(self.itp_push_fail) + ',' + str(self.itp_enhance_fail)))

    def dump_cex(self) -> str:
        return (
                ('P' if self.pushed else ' ') +
                (' | {' + ' , '.join([print_cube(c) for c in self.cex]) + '}') +
                (' | ' + self.origin) +
                (' | ' + str(self.itp_push_fail) + ',' + str(self.itp_enhance_fail)))
    # think about repairing
    # think about contracting
    # think about itp change form


# *** END OF Lemma ***

class FrameCache(object):
    def __init__(self):
        self.frames: Mapping[int, Sequence[Lemma]] = {}  # idx -> list of lemmas

    def _add_lemma(self, lemma, fidx):
        if fidx not in self.frames:
            self.frames[fidx] = []
        self.frames[fidx].append(lemma)

    # *** END OF _add_lemma ***
    def _add_pushed_lemma(self, lemma: Lemma, start, end):
        l_prev = lemma.copy()
        l_prev.pushed = True
        for fidx in range(start, end + 1):
            self._add_lemma(lemma=l_prev, fidx=fidx)

    # *** END OF _add_pushed_lemma ***
    def frame_prop_list(self, fidx):
        if fidx not in self.frames:
            return []
        return [l.expr for l in self.frames[fidx]]
    # *** END OF frame_prop_list ***

    # insert a frame to this one ???


# *** END OF FrameCache ***


# ----------- MAIN CLASS -------------------

class PDR(object):
    def __init__(self, system):
        self.system = system
        init_lemma = Lemma(expr=system.init, cex=[], origin='init')
        self.frames: Sequence[Sequence[Lemma]] = [[init_lemma], []]  # list of list of lemmas

        self.prime_map = dict([(v, TransitionSystem.get_prime(v)) for v in self.system.variables])
        self.primal_map = dict([(TransitionSystem.get_prime(v), v) for v in self.system.variables])

        self.solver = Solver(name='z3')  # use z3 for partial model
        self.valid_solver = self.solver  # we can use btor later
        self.itp_solver = Interpolator(logic=QF_BV)

        self.unblockable_fact = {}  # <n, [ex]> : n -> list of ex, unblocked, used to syn

        self.frames_pushed_idxs_map = {}  # n->idx+1 tried
        self.facts_pushed_idxs_map = {}  # n->idx+1 tried

    # ----------- SOLVING PRIMITIVES -------------------
    def is_valid(self, prop: FNode) -> bool:
        """returns True for valid property, prop : a single formula """
        if self.valid_solver.solve([Not(prop)]):
            return False
        return True

    def is_sat(self, prop: FNode) -> bool:
        """returns True for valid property, prop : a single formula """
        if self.valid_solver.solve([prop]):
            return True
        return False

    # *** END OF is_valid ***
    def get_not_valid_model(self, prop: FNode):
        if self.valid_solver.solve([Not(prop)]):
            return self.valid_solver.get_model()
        return None

    # *** END OF get_not_valid_model ***

    def solve(self, formula: Sequence[FNode], remove_vars=[], keep_vars=None):
        """Provides a satisfiable assignment to the state
        variables that are consistent with the input formula,
        formula : property or a list of property
        returns : a cube : [(v,val)]"""
        # you should know to drop variables here
        # plus tenary simulation ? ast-walker
        if not isinstance(formula, list):
            formula = [formula]
        if self.solver.solve(formula):
            retL = []
            for v, val in self.solver.get_model():
                if v in remove_vars:
                    continue
                if (isinstance(keep_vars, list) or isinstance(keep_vars, set)) and len(
                        keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v, val))
                # retL.append(EqualsOrIff(v, val))
            assert (len(retL) > 0)  # otherwise we are removing too many variables!
            # return And(retL)
            return retL
        return None

    # *** END OF solve ***

    # ----------- FRAME to Properties -------------------
    def frame_prop_list(self, fidx: int):
        return [l.expr for l in self.frames[fidx]]

    def frame_prop(self, fidx: int):  # all prop
        return And([l.expr for l in self.frames[fidx]])

    def frame_prop_select(self, fidx, selector: Callable[[int], bool]):  # which to keep
        return [l.expr for lidx, l in enumerate(self.frames[fidx]) if selector(lidx)]

    def get_inv(self):
        return self.frame_prop(fidx=-1)

    def get_inv_str(self):
        return simplify(self.frame_prop(fidx=-1)).serialize()

    def frame_implies(self, fidx: int, prop: FNode):
        if self.is_valid(Implies(self.frame_prop(fidx), prop)):
            return True
        return False

    def frame_not_implies_model(self, fidx: int, prop: FNode):
        return self.get_not_valid_model(Implies(self.frame_prop(fidx), prop))

    def frame_compatible_w(self, fidx: int, prop: FNode):
        if self.is_sat(And(self.frame_prop_list(fidx) + [prop])):
            return True
        return False

    # ----------- FRAME Checks -------------------
    def is_last_two_frames_inductive(self):
        """Checks if last two frames are equivalent (no need to change variable to prime)"""
        if len(self.frames) > 1 and \
                self.is_valid(Implies(self.frame_prop(fidx=-1), self.frame_prop(fidx=-2))):
            return True
        return False

    def sanity_check_safe_inductive_inv(self, prop: FNode):
        T = self.system.trans
        inv = self.get_inv()
        inv_prime = inv.substitute(self.prime_map)
        assert (self.is_valid(Implies(self.system.init, inv)))
        assert (self.is_valid(Implies(And(inv, T), inv_prime)))
        assert (self.is_valid(Implies(inv, prop)))

    def sanity_check_imply(self):
        assert (len(self.frames) > 1)
        T = self.system.trans
        for fidx in range(1, len(self.frames)):
            next_frame = self.frame_prop(fidx=fidx)
            next_frame = next_frame.substitute(self.prime_map)
            assert (self.is_valid(Implies(And(self.frame_prop(fidx - 1), T), next_frame)))
            # if model is not None:
            #    print ('Bug, F%d and T -/-> F%d' % (fidx-1, fidx))
            #    assert (False)

    def sanity_check_frame_monotone(self):
        assert (len(self.frames) > 1)
        for fidx in range(1, len(self.frames)):
            valid = self.is_valid(Implies(self.frame_prop(fidx - 1), self.frame_prop(fidx)))
            if not valid:
                self.dump_frames()
                print('Bug, not monotone, F%d -> F%d' % (fidx - 1, fidx))

                print('Bug lemmas in F%d' % fidx)
                for lemmaIdx, lemma in enumerate(self.frame_prop_list(fidx)):
                    model = self.get_not_valid_model(Implies(self.frame_prop(fidx - 1), lemma))
                    if model is not None:
                        print(' l%d : ' % lemmaIdx, lemma.serialize())
                assert False

    # ----------- PRINTINGs -------------------
    def dump_frames(self, toStr=False):
        retS = []

        def _printStr(*argl, **argd):
            if toStr:
                retS.append(''.join(argl))
            else:
                print(*argl, **argd)

        _printStr('---------- Frames DUMP ----------')
        for fidx, f in enumerate(self.frames):
            _printStr('Frame : %d' % fidx)
            for lidx, lemma in enumerate(f):
                ptr = '*' if self.frames_pushed_idxs_map.get(fidx, 0) == lidx else ' '
                lemmaStr = lemma.dump_expr()
                _printStr('  %s l%d: ' % (ptr, lidx), lemmaStr)
            if self.frames_pushed_idxs_map.get(fidx, 0) == lidx + 1:
                _printStr('    all tried to push')

            _printStr('  CEX blocked :')
            for lidx, lemma in enumerate(f):
                ptr = '*' if self.frames_pushed_idxs_map.get(fidx, 0) == lidx else ' '
                cexStr = lemma.dump_cex()
                _printStr('  %s c%d: ' % (ptr, lidx), cexStr)
            if self.frames_pushed_idxs_map.get(fidx, 0) == lidx + 1:
                _printStr('    all tried to push')

            if fidx in self.unblockable_fact:
                _printStr('  facts # : %d' % len(self.unblockable_fact[fidx]))
                for cidx, fact in enumerate(self.unblockable_fact[fidx]):
                    _printStr('    f%d: ' % cidx, print_cube(fact))

        _printStr('---------- END Frames DUMP ----------')
        return '\n'.join(retS)

    # *** END OF dump_frames ***

    # ----------- FRAME HANDLing  -------------------

    def _add_lemma(self, lemma: Lemma, fidx: int):
        if fidx == len(self.frames):
            self.frames[fidx].append([])
        assert fidx < len(self.frames)
        self.frames[fidx].append(lemma)

    # *** END OF _add_lemma ***
    def _add_pushed_lemma(self, lemma: Lemma, start: int, end: int):
        l_prev = lemma.copy()
        l_prev.pushed = True
        for fidx in range(start, end + 1):
            self._add_lemma(lemma=l_prev, fidx=fidx)

    # *** END OF _add_pushed_lemma ***
    def _add_fact(self, fact: Sequence[Tuple[FNode, FNode]], fidx):
        if fidx not in self.unblockable_fact:
            self.unblockable_fact[fidx] = []
        assert fact not in self.unblockable_fact[fidx]
        self.unblockable_fact[fidx].append(fact)

    # ----------- TRANS - related  -------------------

    # you may want to have the interpolant here
    # used in recursive_block  and  get_bad_state_from_property_invalid_after_trans
    # use frame_prop_list for prevF !!!
    # --------------------------------------------------------------
    # NOTE:
    #       to be used as get_pre_post_state_from_property_invalid_after_trans:
    #       init = None, findItp = False, get_post_state = True
    def solveTrans(self, prevF, T, prop, variables, init,
                   remove_vars=[], keep_vars=None, findItp=False, get_post_state=False):
        assert (isinstance(prevF, list))
        # prevF /\ T(p, prime) --> not prop, if sat
        debug('      [solveTrans] Property:', prop.serialize())
        debug('      [solveTrans] var will => prime')
        # print ('      [solveTrans] prevF:', prevF)
        debug('      [solveTrans] use Init:', init is not None)

        if init is None:
            f = prevF + [T, Not(prop.substitute(self.prime_map))]
        else:
            f = [Or(And(prevF + [T]), init.substitute(self.prime_map)), Not(prop.substitute(self.prime_map))]
        # print (f)
        if self.solver.solve(f):
            model = self.solver.get_model()
            pre_ex = []
            post_ex = []
            for v, val in model:
                if v in variables:
                    # pre_ex
                    if v in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                        continue
                    pre_ex.append((v, val))
                elif get_post_state:
                    v_primal = self.primal_map[v]
                    if v_primal in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v_primal not in keep_vars:
                        continue
                    post_ex.append((v_primal, val))
            assert (len(pre_ex) > 0)  # otherwise we are removing too many variables!
            # return And(retL)
            return pre_ex, post_ex, None
        Itp = None
        if findItp:
            if init is None:
                a = And(prevF + [T])
                b = Not(prop.substitute(self.prime_map))
            else:
                a = f[0]
                b = f[1]
            Itp = self.itp_solver.binary_interpolant(a=a, b=b)
            Itp = And(Itp)
            Itp = Itp.substitute(self.primal_map)
            if Config_simplify_itp:
                Itp = simplify(Itp)
            debug('    [solveTrans] get itp: ', Itp.serialize())
            # pause()
        return None, None, Itp

    # *** END OF solveTrans ***

    # used in check_property, check_init_failed
    # not in push_lemma, because we also want the pre-&post-states
    def get_bad_state_from_property_invalid_after_trans(self, prop, idx, use_init, remove_vars=[], keep_vars=None):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        assert (idx >= 0)
        debug('    [F%d -> prop]' % idx)
        md, _, _ = self.solveTrans(self.frame_prop_list(idx),
                                   T=self.system.trans, prop=prop,
                                   init=self.system.init if use_init else None,
                                   variables=self.system.variables,
                                   remove_vars=remove_vars, keep_vars=keep_vars, findItp=True, get_post_state=False)
        # no need for itp here
        # pause()
        return md

    # *** END OF get_bad_state_from_property_invalid_after_trans ***

    def do_recursive_block(self, cube, idx, cex_origin, remove_vars=[], keep_vars=None):
        assert isinstance(cex_origin, str)

        priorityQueue = []
        debug('      [block] Try @F%d' % idx, print_cube(cube))

        prop = _cube2prop(cube)
        if self.frame_implies(idx, prop):
            debug('      [block] already blocked by F%d' % idx)
            return True

        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve(
                    [self.system.init] + [EqualsOrIff(v, val) for v, val in cex])
                assert (model_init_frame is not None)
                debug('      [block] CEX found!')
                return False

            prop = _cube2prop(cex)  # Not(And([EqualsOrIff(v,val) for v,val in cex]))

            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            debug('      [block] check at F%d -> F%d : ' % (fidx - 1, fidx), str(prop))
            # if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        debug ('      [block] CEX is reachable -- direct init!')
            #        return False

            model, _, itp = self.solveTrans(self.frame_prop_list(fidx - 1) + ([prop] if Config_rm_cex_in_prev else []),
                                            T=self.system.trans, prop=prop,
                                            variables=self.system.variables,
                                            init=self.system.init,
                                            remove_vars=remove_vars, keep_vars=keep_vars, findItp=True,
                                            get_post_state=False)

            if model is None:
                lemma = Lemma(expr=itp, cex=[cex], origin=cex_origin)
                self._add_lemma(lemma=lemma, fidx=fidx)
                self._add_pushed_lemma(lemma=lemma, start=1, end=fidx - 1)
                heapq.heappop(priorityQueue)  # pop this cex
            else:
                # model is not None
                debug('      [block] push to queue, F%d' % (fidx - 1), print_cube(model))
                heapq.heappush(priorityQueue, (fidx - 1, model))
        debug('      [block] Succeed, return.')
        return True

    # *** END OF do_recursive_block ***

    def try_recursive_block(self, cube, idx, cex_origin, frame_cache: FrameCache, remove_vars=[], keep_vars=None):
        assert isinstance(cex_origin, str)

        priorityQueue = []
        debug('      [block] Try @F%d' % idx, print_cube(cube))

        prop = _cube2prop(cube)

        if self.is_valid(Implies(And(self.frame_prop_list(idx) + frame_cache.frame_prop_list(idx)), prop)):
            debug('      [block] already blocked by F%d' % idx)
            return True

        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve(
                    [self.system.init] + [EqualsOrIff(v, val) for v, val in cex])
                assert (model_init_frame is not None)
                debug('      [block] CEX found!')
                return False

            prop = _cube2prop(cex)  # Not(And([EqualsOrIff(v,val) for v,val in cex]))

            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            debug('      [block] check at F%d -> F%d : ' % (fidx - 1, fidx), str(prop))
            # if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        print ('      [block] CEX is reachable -- direct init!')
            #        return False

            model, _, itp = self.solveTrans(
                self.frame_prop_list(fidx - 1) \
                + frame_cache.frame_prop_list(fidx - 1) \
                + ([prop] if Config_rm_cex_in_prev else []),
                T=self.system.trans, prop=prop,
                variables=self.system.variables,
                init=self.system.init,
                remove_vars=remove_vars, keep_vars=keep_vars, findItp=True, get_post_state=False)

            if model is None:
                lemma = Lemma(expr=itp, cex=[cex], origin=cex_origin)
                frame_cache._add_lemma(lemma=lemma, fidx=fidx)
                frame_cache._add_pushed_lemma(lemma=lemma, start=1, end=fidx - 1)
                heapq.heappop(priorityQueue)  # pop this cex
            else:
                # model is not None
                debug('      [block] push to queue, F%d' % (fidx - 1), print_cube(model))
                heapq.heappush(priorityQueue, (fidx - 1, model))
        debug('      [block] Succeed, return.')
        return True

    # *** END OF try_recursive_block ***

    # ----------- PROCEDURES -------------------

    def check_init_failed(self, prop, remove_vars, keep_vars):
        init_cex = self.frame_not_implies_model(fidx=0, prop=prop)
        print("[Checking init] F0 and not P")
        if init_cex is not None:
            print("[Checking init] Property failed at INIT")
            print("[Checking init] CEX: ", print_cube(init_cex))
            return True
        print("[Checking init]  F0 and T and not P'")
        init_cex = self.get_bad_state_from_property_invalid_after_trans(
            prop=prop, idx=0, use_init=True, remove_vars=remove_vars, keep_vars=keep_vars)
        if init_cex is not None:
            print("[Checking init] Property failed at F1")
            print("[Checking init] CEX @F0: ", print_cube(init_cex))
            return True
        print("[Checking init] Done")
        return False

    # *** END OF check_init_failed ***

    def check_property(self, prop, remove_vars=[], keep_vars=None):
        """Property Directed Reachability approach without optimizations."""
        print("[Checking property] Property: %s." % prop)

        if self.check_init_failed(prop, remove_vars, keep_vars):
            return False

        # self._add_lemma(fidx = 1, lemma = prop) : no need
        # its interpolant may be too small

        while True:
            self.sanity_check_frame_monotone()
            self.sanity_check_imply()
            if Config_debug_print:
                self.dump_frames()
            print('Total Frames: %d, L %d ' % (len(self.frames), len(self.frames[-1])))
            pause()

            # frame[-1] /\ T -> not (prop)
            cube = self.get_bad_state_from_property_invalid_after_trans(
                prop=prop, idx=len(self.frames) - 1, use_init=False, remove_vars=remove_vars, keep_vars=keep_vars)

            debug('[Checking property] Get cube: ', cube, ' @F%d' % (len(self.frames) - 1))
            # cube is list of (var, assignments)
            if cube is not None:
                # Blocking phase of a bad state
                if not self.do_recursive_block(cube, len(self.frames) - 1, cex_origin='prop', remove_vars=remove_vars,
                                               keep_vars=keep_vars):
                    print("[Checking property] Bug found at step %d" % (len(self.frames)))
                    return False
                else:
                    debug("[Checking property] Cube blocked '%s'" % print_cube(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.is_last_two_frames_inductive():
                    print("[Checking property] The system is safe, frame : %d" % len(self.frames))
                    return True
                else:
                    print("[Checking property] Adding frame %d..." % (len(self.frames)))
                    self.frames.append([])
                    self.push_lemma_from_the_lowest_frame(remove_vars, keep_vars)
                    if self.is_last_two_frames_inductive():
                        print("[Checking property] The system is safe, frame : %d" % len(self.frames))
                        return True

    # *** END OF check_property ***

    # put too few in the
    def push_lemma_from_the_lowest_frame(self, remove_vars, keep_vars):
        start_frame = 1  # let's try not to worry about caching this at this time
        # do not push from the initial frame
        print('[pushes] F%d --- F%d' % (start_frame, len(self.frames) - 2))
        for fidx in range(start_frame, len(self.frames) - 1):
            self.push_lemma_from_frame(fidx, remove_vars, keep_vars)

    # *** END OF push_lemma_from_the_lowest_frame ***

    # ----------- !!! PUSH LEMMA !!! -------------------
    def push_lemma_from_frame(self, fidx, remove_vars, keep_vars):
        assert (len(self.frames) > fidx + 1)
        assert (len(self.frames[fidx]) > 0)

        # 1. push facts
        start_fact_idx = self.facts_pushed_idxs_map.get(fidx, 0)
        end_fact_idx = len(self.unblockable_fact.get(fidx, []))
        if fidx in self.unblockable_fact:
            for factIdx in range(start_fact_idx, end_fact_idx):
                fact = self.unblockable_fact[fidx][factIdx]
                # once a fact always a fact
                if fact not in self.unblockable_fact.get(fidx + 1, []):
                    self._add_fact(fact=fact, fidx=fidx + 1)
        self.facts_pushed_idxs_map[fidx] = end_fact_idx

        ## push lemmas
        start_lemma_idx = self.frames_pushed_idxs_map.get(fidx, 0)
        end_lemma_idx = len(self.frames[fidx])

        unpushed_lemmas = []  # list of (lidx, lemma, prev_ex, post_ex )

        # 1. try direct push
        for lemmaIdx in range(start_lemma_idx, end_lemma_idx):
            lemma: Lemma = self.frames[fidx][lemmaIdx]
            if lemma.pushed:
                continue
            debug('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx + 1), (lemma.serialize()))

            prev_ex, post_ex, _ = \
                self.solveTrans(prevF=self.frame_prop_list(fidx),
                                T=self.system.trans, prop=lemma.expr, variables=self.system.variables,
                                init=None, remove_vars=remove_vars, keep_vars=keep_vars,
                                findItp=False, get_post_state=True)
            # variables there is to distinguish vars and prime vars

            if prev_ex is None:  # post_ex should be none also
                # push is successful
                assert (post_ex is None)
                debug('  [push_lemma F%d] Succeed in pushing l%d!' % (fidx, lemmaIdx))
                self._add_lemma(lemma.direct_push(), fidx=fidx + 1)  # together with its cex
            else:  # there is a failing model
                # store if temporarily and we will decide how to deal with them
                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
        # finish pushing all that can be pushed
        # start to deal with unpushed

        # 2. handled unpushed lemmas
        for lemmaIdx, lemma, prev_ex, post_ex in unpushed_lemmas:
            if len(lemma.cex) == 0:
                debug('  [push_lemma F%d] will give up on lemma as it blocks None, ' % fidx,
                      'l' + str(lemmaIdx) + ':', lemma.serialize())
                continue
            # 2.1 if subsume, then we don't need to worry about
            if lemma.subsume_by_frame(fidx=fidx + 1, pdr=self):  # should not touch frames in pdr
                continue
            # 2.2 try itp repair
            itp_fc = FrameCache()  # self as an fc also, but the solver etc also
            cex_failed, itp = lemma.try_itp_push(fc=itp_fc, src_fidx=fidx, pdr=self, remove_vars=remove_vars,
                                                 keep_vars=keep_vars)
            # itp is also in the framecache, should not touch frames in pdr
            # itp is a Lemma object
            if cex_failed:
                assert (itp is None)
                # not pushable
                debug('  [push_lemma F%d] skip r-block l%d :' % (fidx, lemmaIdx), lemma.serialize(),
                      ' as its cex cannot be pushed.')
                continue

            debug('  [push_lemma F%d] try sygus repair l%d :' % (fidx, lemmaIdx), lemma.serialize())
            # 2.3 sygus repair
            if Config_use_sygus:
                sygus_hint: Lemma = lemma._try_sygus_repair(fidx=fidx,
                                                            lemmaIdx=lemmaIdx, post_ex=post_ex, new_itp=itp, pdr=self,
                                                            remove_vars=remove_vars,
                                                            keep_vars=keep_vars)  # should not touch frames in pdr
            else:
                sygus_hint = None
            if sygus_hint is not None:
                # succeed in repair
                self._add_lemma(lemma=sygus_hint, fidx=fidx + 1)
                self._add_pushed_lemma(lemma=sygus_hint, start=1, end=fidx)
                debug('  [push_lemma F%d] repair l%d :' % (fidx, lemmaIdx), lemma.serialize())
                debug('  [push_lemma F%d] get l%d :' % (fidx, lemmaIdx), sygus_hint.serialize())
                continue

            # 2.4 try contraction
            debug('  [push_lemma F%d] try strengthening l%d :' % (fidx, lemmaIdx), lemma.serialize())
            pause()
            strengthen_fc = FrameCache()  # self as an fc also, but the solver etc also
            prop_succ, all_succ, rmBnd, unblockable_cube = lemma.try_strengthen(
                fc=strengthen_fc, bnd=Config_strengthen_effort_for_prop, src_fidx=fidx, pdr=self, prev_ex=prev_ex,
                remove_vars=remove_vars, keep_vars=keep_vars)
            # full/prop itself/bad_state
            if all_succ or prop_succ:
                debug('  [push_lemma F%d] strengthened l%d :' % (fidx, lemmaIdx), lemma.serialize(),
                      " with extra lemma, ", 'A' if all_succ else 'P')
                self.merge_frame_cache(strengthen_fc)
                continue

            if (unblockable_cube is not None) and (rmBnd >= 0):
                self._add_fact(fact=unblockable_cube, fidx=fidx)
            else:
                assert (rmBnd < 0)  # bound limit reached

            # try strengthen, but unable to even strengthen the main prop in
            # the given time
            debug('  [push_lemma F%d] unable to push l%d :' % (fidx, lemmaIdx), lemma.serialize())
            debug('  [push_lemma F%d] use new itp l%d :' % (fidx, lemmaIdx), itp.serialize())
            self.merge_frame_cache(itp_fc)

            # get its recursive blocked
            # try itp push : given a framcecache?
            # try recurisve push : given a framecache?
            # try sygus push

        # F. update pushed
        self.frames_pushed_idxs_map[fidx] = end_lemma_idx

    # *** END OF push_lemma_from_frame ***
    def merge_frame_cache(self, fc: FrameCache):
        for fidx, lemmas in fc.frames.items():
            for lemma in lemmas:
                self._add_lemma(lemma=lemma, fidx=fidx)
    # *** END OF merge_frame_cache ***


def test_naive_pdr():
    width = 32
    cnt = BaseAddrCnt(width)
    prop = cnt.neq_property(1 << (width - 1), 1, 1)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_safe_inductive_inv(prop)
    pdr.dump_frames()
    print('inv: ', simplify(pdr.get_inv()).serialize())


def test_naive_pdr_2cnt():
    width = 32
    cnt = TwoCnt(width, zero_init=True)
    # prop_good = cnt.false_property(65536-1001,1000)
    prop = cnt.neq_property(65536 - 1000, 1000)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_safe_inductive_inv(prop)
    pdr.dump_frames()
    print('inv: ', simplify(pdr.get_inv()).serialize())


def test_naive_pdr_2cnt_noload():
    width = 16
    cnt = TwoCntNoload(width, zero_init=True)
    # prop_good = cnt.false_property(65536-1001,1000)
    prop = cnt.neq_property(65536 - 1000, 1000)
    pdr = PDR(cnt)
    pdr.check_property(prop)
    pdr.sanity_check_imply()
    pdr.sanity_check_frame_monotone()
    pdr.sanity_check_safe_inductive_inv(prop)
    pdr.dump_frames()
    print('inv: ', simplify(pdr.get_inv()).serialize())


if __name__ == '__main__':
    test_naive_pdr_2cnt_noload()
