"""SyGuS"""

from pysmt.shortcuts import Not, And, Or, EqualsOrIff
from pysmt.shortcuts import Solver

from efmc.engines.sygus_pdr.graphreach import GraphReach
from efmc.engines.sygus_pdr.utilfunc import _get_unified_width

Config_expand_values = False
Config_use_trans = False
Config_use_init = True
# Config_use_Fminus2_imply = Config_use_trans
Config_use_facts = True
Config_smtlib2_daggify = False  # maybe make it to True ?


def _to_type_string(v):
    if v.get_type().is_bool_type():
        return 'Bool'
    assert (v.get_type().is_bv_type())
    return '(_ BitVec %d)' % v.bv_width()


def sanitize_name(s):
    goodname = set(s) <= set('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._')
    if not goodname:
        return '|' + s + '|'
    return s  # normal


def _to_name_type(v):  # v should be a pysmt v
    assert (v.is_symbol())
    return '(' + sanitize_name(v.symbol_name()) + " " + _to_type_string(v) + ')'


def _to_name_type_suffix_no_p(v, suffix):  # v should be a pysmt v
    assert (v.is_symbol())
    return sanitize_name(v.symbol_name() + suffix) + " " + _to_type_string(v)


def _to_args(vl):
    return '(' + (' '.join([_to_name_type(v) for v in vl])) + ')'


def _to_tr_args(vl, vp):
    return '(' + (' '.join([_to_name_type(v) for v in vl] + [_to_name_type(v) for v in vp])) + ')'


def _gen_smt2(fn):
    return fn.to_smtlib(daggify=Config_smtlib2_daggify)


def _const_to_str(fn):
    if fn.is_bv_constant():
        return '#b' + fn.bv_str()
    elif fn.is_bool_constant():
        return 'true' if fn.is_true() else 'false'
    assert False  # unknown type


def _sanity_check_no_conflict(facts, blocked, vset):
    solver = Solver()

    facts_or_list = []
    for cube in facts:
        # facts with more vars
        facts_or_list.append(And([EqualsOrIff(v, val) for v, val in cube.items() if v in vset]))
    if len(facts_or_list) > 0:
        solver.add_assertion(Or(facts_or_list))

    for cube in blocked:
        solver.add_assertion(Not(And([EqualsOrIff(v, val) for v, val in cube.items() if v in vset])))

    satisfiable = solver.solve()
    if not satisfiable:
        print('cex and facts conflicts: unsat!')
        print('----Facts----')
        for cube in facts:
            print(cube)
        print('----Blocks----')
        for cube in blocked:
            print(cube)

    assert satisfiable  # we expect it is satisfiable,


# get the variable of ex
# get the operators of lemma
# get the unblockable fact of these variables
#    and all other with more variables,
# get the cexs of these variables or fewer
# sygus  --- what if there are conflicts??? (should not be)
# get back and put to

# but if you try with F[fidx - 1] /\ T --> INV[fidx]
# not INV(blocked[fidx]), but you don't know if it is blocked/unblocked
# INV(fact[fidx]), and then you don't need to try to push, because you already pushed
# but in this way you are actually pushing the cex/facts


# synthesize a stronger one to push?
# variables?
# F[fidx - 2] /\ T --> INV[fidx - 1 ]
# not INV (blocked)
# INV(fact) /\ INV(fact[fidx])
# put in self.frames?
# try push this INV?
# threshold in construction ? grammar may be not enough?


sygus_template = """

(set-logic BV)

{predefs}

(synth-fun INV 
   {args} Bool
( (Conj Bool) (Disj Bool) (Literal Bool) (Atom Bool)
  {nonterminals}
)
(
    (Conj Bool (Disj 
                (and Disj Conj)))
    (Disj Bool (Literal 
                (or Literal Disj)))
    (Literal Bool (Atom
                (not Atom)))
    (Atom Bool (
      {comps}
      ))
      {evcs}
   ))

{Init}
{Fminus2}
{Tr}

{vdefs}

{blocks}
{facts}
{imply}
{init_imply_stx}

(check-synth)

"""


# (E0 Bool )
#    (E2 (_ BitVec 2) (V2 (bvadd E2 E2)))
#    (V2 (_ BitVec 2) (base addr cnt C2 V2))
#    (C2 (_ BitVec 2) (#b00 #b01 #b10 #b11))
# define F-2
# define Tr
# define vars

# (constraint (not (INV #b10 #b00 #b00))) # it can be fewer vars, what to do?
# (constraint (INV #b10 #b00 #b00))

# (constraint (=> (and (F-2 %allvars%) (Tr %allvars%)) (INV %vars%)))
# (constraint (=> (F-2 %allvars%) ))


class BvConstructs:
    def __init__(self, Vars, Arithms, Comps, Consts, Concats, Extracts, Rotates, Exts, Unary):
        self.Vars, self.Arithms, self.Comps, self.Consts, self.Concats, self.Extracts, \
            self.Rotates, self.Exts, self.Unary = \
            Vars, Arithms, Comps, Consts, Concats, Extracts, Rotates, Exts, Unary
        # need to convert to string (op, consts, vars)

    def empty(self):
        return len(self.Vars) == 0 and len(self.Arithms) == 0 and len(self.Comps) == 0 \
            and len(self.Consts) == 0 and len(self.Concats) == 0 and len(self.Extracts) == 0 and \
            len(self.Rotates) == 0 and len(self.Exts) == 0 and len(self.Unary) == 0

    @staticmethod
    def width_to_type(width):
        assert (width >= 0)
        if width == 0:
            return 'Bool'
        return '(_ BitVec %d)' % width


# 0 for bool
# self.BvUnary = {}    # width -> set[ops]
# self.BvOps = {}      # you need to know the width also : width -> set[ops] (same width)
# self.BvComps = {}    # you need to know the width also : width -> set[ops] (same width)
# self.BvConsts = {}   # width -> set[consts (should be string already)] # const eq?
# self.BvConcats = {}  # result width -> set[(width1, width2)]
# self.BvExtracts = {} # result width -> set[(input width, h, l)]
# self.BvRotates = {}   # result width -> set[(op, param)]
# self.BvExts = {}     # result width -> set[(op, param, input width )] op


class SyGusQueryGen:
    ## QUESTION: DO YOU NEED TO KNOW BLOCKED CEX F_idx_minus2 ???
    ## YOU CAN TRY?

    ## (prev /\ T => new ) => itp => cex_next

    # the use of ctg is only to get varset

    def __init__(self,
                 primal_vars, prime_vars,
                 T, F_idx_minus2, Init,
                 inv_var_set, facts_on_inv_vars, cexs_on_inv_vars,
                 sorted_inv_var_set, sorted_allvars, sorted_prime_vars,
                 op_obj, cache_mode=False):
        # in cache mode, will not recompute
        # self.LangConstructs

        assert (Config_use_trans or Config_use_facts)  # you have to use at least one pos example
        if Config_use_trans:
            assert (isinstance(F_idx_minus2, list))
        else:
            print('[SyGuS] Warning: please note, F_idx_minus2 is not used!')
            # assert (F_idx_minus2 is None)

        self.allvars = sorted_allvars
        self.prime_vars = sorted_prime_vars
        self.variable_set = inv_var_set
        self.ordered_vars = sorted_inv_var_set

        # list of dict (v -> val)
        self.facts = facts_on_inv_vars  # _get_cubes_with_more_var(facts, self.variable_set)  # exists a = 1 b = 1 (c ?)
        # list of dict (v -> val)
        self.blocked_cexs = cexs_on_inv_vars  # _get_cubes_with_fewer_var(blocked_cexs, self.variable_set) # (not a = 1)

        _sanity_check_no_conflict(self.facts, self.blocked_cexs, self.variable_set)

        if Config_use_trans:
            self.F_prev = F_idx_minus2
            self.T = T
        if Config_use_init:
            self.Init = Init

        # fix the above, you need to extract first -- fixed
        if not cache_mode:
            self.LangConstructs = {}  # bitwidth -> BvConstructs
            self._to_bv_constructs(op_obj)
            self._remove_unused_width()

            self.functs = {}  # func name -> def string # currently no use
            self.funct_replace = {}  # func name -> text to replace

    def set_syntax_cache(self, LangConstructs, functs, funct_replace):
        self.LangConstructs = LangConstructs
        self.functs = functs
        self.funct_replace = funct_replace

    def get_syntax_cache(self):
        return self.LangConstructs, self.functs, self.funct_replace

        # def get_enhanced_itp(self, fn = 'cex-idx.smt2'):

    #    self.gen_sygus_query(fn)
    # assert (False) # need to implement here about running cvc4 and read in

    def _to_bv_constructs(self, opextract):  # can be moved to cegpbe
        # opextract -> self.LangConstructs
        # deal with variables
        for v in self.variable_set:
            w = _get_unified_width(v)
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            # print (v,'width=',w)
            self.LangConstructs[w].Vars.append(sanitize_name(v.symbol_name()))
            # print (self.LangConstructs[w].Vars)

        print(opextract.BvUnary)
        print(opextract.BvOps)
        for w, ops in opextract.BvUnary.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Unary = ops

        for w, ops in opextract.BvOps.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Arithms = ops

        for w, ops in opextract.BvComps.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Comps = ops

        for w, consts in opextract.BvConsts.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Consts = consts

        for w, concats in opextract.BvConcats.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Concats = concats

        for w, extracts in opextract.BvExtracts.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Extracts = extracts

        for w, rotates in opextract.BvRotates.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Rotates = rotates

        for w, exts in opextract.BvExts.items():
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs(Vars=[], Arithms=[], Comps=[], Consts=[], Concats=[], Extracts=[],
                                                      Rotates=[], Exts=[], Unary=[])
            self.LangConstructs[w].Exts = exts

        # sanity check, when it is referring an arg, arg with that w should exist
        for w, constr in self.LangConstructs.items():
            for w1, w2 in constr.Concats:
                assert (not self.LangConstructs[w1].empty())
                assert (not self.LangConstructs[w2].empty())
            for wi, h, l in constr.Extracts:
                assert (not self.LangConstructs[wi].empty())
            for op, p, wi in constr.Exts:
                assert (not self.LangConstructs[wi].empty())

    def gen_sygus_query(self, sygus_fn):
        # finishing the syntax tree
        comps, evcs, nt_stx = self._to_sygus_tree()
        # '(constraint (INV '
        facts_stx = self._to_facts()
        # '(constraint (not (INV' ...
        blocks_stx = self._to_blocks()
        # '(define-fun Fminus2 '
        f_minus_2_stx = self._gen_f_minus_2() if Config_use_trans else ''
        # '(define-fun Tr '
        tr_stx = self._gen_tr() if Config_use_trans else ''
        # '(define-fun Init '
        init_stx = self._gen_init() if Config_use_init else ''

        # ['(declare-var V'
        # ['(declare-var P'
        vp_def_stx = self._gen_def_states()
        # '(constraint (=> (and (Fminus2 {argV}) (Tr {argV} {argP})) (INV {argInvP})))'
        imply_stx = self._gen_Fminus2_Tr_imply_constraint() if Config_use_trans else ''
        # '(constraint (=> (Fminus2 {argP}) (INV {argInvP})))'
        # below is not necessary
        # monotone_stx = self._gen_Fminus2_imply_constraint() if Config_use_Fminus2_imply else ''
        # currently nothing
        init_imply_stx = self._gen_Init_imply_constraint() if Config_use_init else ''

        predefs = '\n'.join([d for _, d in self.functs.items()])
        # the var list
        args = _to_args(self.ordered_vars)

        sygus_query = sygus_template.format(predefs=predefs, args=args,
                                            comps=comps, evcs=evcs, Fminus2=f_minus_2_stx,
                                            Init=init_stx, Tr=tr_stx, vdefs=vp_def_stx, blocks=blocks_stx,
                                            facts=facts_stx, imply=imply_stx, init_imply_stx=init_imply_stx,
                                            nonterminals=nt_stx)

        with open(sygus_fn, 'w') as fout:
            fout.write(sygus_query)

    def _gen_def_states(self):  # -> vp_def_stx
        v_def = ['(declare-var ' + _to_name_type_suffix_no_p(v, 'V') + ')' for v in self.allvars]
        p_def = ['(declare-var ' + _to_name_type_suffix_no_p(v, 'P') + ')' for v in self.allvars]
        return '\n'.join(v_def) + '\n' + '\n'.join(p_def)

    def _gen_Fminus2_Tr_imply_constraint(self):  #
        template = '(constraint (=> (and (Fminus2 {argV}) (Tr {argV} {argP}) (INV {argInvV})) (INV {argInvP})))'
        argv = ' '.join([sanitize_name(v.symbol_name() + 'V') for v in self.allvars])
        argp = ' '.join([sanitize_name(v.symbol_name() + 'P') for v in self.allvars])
        arginvv = ' '.join([sanitize_name(v.symbol_name() + 'V') for v in self.ordered_vars])
        arginvp = ' '.join([sanitize_name(v.symbol_name() + 'P') for v in self.ordered_vars])
        return template.format(argV=argv, argP=argp, argInvV=arginvv, argInvP=arginvp)

    def _gen_Init_imply_constraint(self):  #
        template = '(constraint (=> (Init {argV}) (INV {argInvV})))'
        argv = ' '.join([sanitize_name(v.symbol_name() + 'V') for v in self.allvars])
        arginvv = ' '.join([sanitize_name(v.symbol_name() + 'V') for v in self.ordered_vars])
        return template.format(argV=argv, argInvV=arginvv)

    def _gen_Fminus2_imply_constraint(self):  #
        template = '(constraint (=> (Fminus2 {argP}) (INV {argInvP})))'
        argv = ' '.join([sanitize_name(v.symbol_name() + 'V') for v in self.allvars])
        argp = ' '.join([sanitize_name(v.symbol_name() + 'P') for v in self.allvars])
        arginvp = ' '.join([sanitize_name(v.symbol_name() + 'P') for v in self.ordered_vars])
        return template.format(argV=argv, argP=argp, argInvP=arginvp)

    def _gen_f_minus_2(self):  # -> f_minus_2_stx
        return '(define-fun Fminus2 ' + _to_args(self.allvars) + ' Bool ' + _gen_smt2(And(self.F_prev)) + ')'

    def _gen_init(self):  # -> init_stx
        return '(define-fun Init ' + _to_args(self.allvars) + ' Bool ' + _gen_smt2(self.Init) + ')'

    def _gen_tr(self):  # -> tr_stx
        return '(define-fun Tr ' + _to_tr_args(self.allvars, self.prime_vars) + \
            ' Bool ' + _gen_smt2(And(self.T)) + ')'

    def _to_blocks(self):  # -> blocks_stx
        blocks_stx = []
        for cube in self.blocked_cexs:
            statement = '(constraint (not (INV'
            for v in self.ordered_vars:
                if v in cube:
                    statement += ' ' + _const_to_str(cube[v])
                else:  # not in, then we have a choice
                    if Config_expand_values:
                        assert False  # TODO: not implemented, probably not needed
                    else:
                        statement += ' ' + sanitize_name(v.symbol_name() + 'V')  # we expect it to be forall
            statement += ')))'
            blocks_stx.append(statement)
        return '\n'.join(blocks_stx)

    def _to_facts(self):  # -> facts_stx
        facts_stx = []
        for cube in self.facts:  # self.facts is a list of dict
            statement = '(constraint (INV '
            for v in self.ordered_vars:
                if v in cube:
                    statement += ' ' + _const_to_str(cube[v])
                else:  # not in, then we have a choice
                    if Config_expand_values:
                        assert False  # TODO: not implemented, probably not needed
                    else:
                        statement += ' ' + sanitize_name(v.symbol_name() + 'V')  # we expect it to be forall

                        # alert
                        print('Warning: expand V for facts')
                        print(statement)
                        # assert (False) # warning
            statement += '))'
            facts_stx.append(statement)

            # facts_stx.append( \
            #    '(constraint (INV ' + \
            #    ' '.join([_const_to_str( cube[v] ) for v in self.ordered_vars]) + \
            #    '))' )
        return '\n'.join(facts_stx)

    def _to_sygus_tree(self):  # generate comps, evcs # update self.funct self.funct_replace
        # for each bv, at least have the eq
        comps = []
        for width, constr in self.LangConstructs.items():
            comps.append('(= E%d E%d)' % (width, width))
            for op in constr.Comps:
                if op != '=':
                    comps.append('(%s E%d E%d)' % (op, width, width))
        comps = ' '.join(comps)

        nonterminals = []
        evcs = ''

        for width, constr in self.LangConstructs.items():
            tp = BvConstructs.width_to_type(width)
            evcs += ('(E%d' % width) + ' ' + tp + ' ('
            nonterminals.append(('E%d' % width, tp))

            if constr.Vars:
                evcs += 'V%d ' % width
                nonterminals.append(('V%d' % width, tp))
            if constr.Consts:
                evcs += 'C%d ' % width
                nonterminals.append(('C%d' % width, tp))
            if constr.Arithms or constr.Unary:
                evcs += 'Arithm%d ' % width
                nonterminals.append(('Arithm%d' % width, tp))
            if constr.Concats:
                evcs += 'Concat%d ' % width
                nonterminals.append(('Concat%d' % width, tp))
            if constr.Extracts:
                evcs += 'Extract%d ' % width
                nonterminals.append(('Extract%d' % width, tp))
            if constr.Rotates:
                evcs += 'Rotate%d ' % width
                nonterminals.append(('Rotate%d' % width, tp))
            if constr.Exts:
                evcs += 'Ext%d ' % width
                nonterminals.append(('Ext%d' % width, tp))

            evcs += '))\n'

            # print (constr.Vars)
            if constr.Vars:
                evcs += ('(V%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(constr.Vars)  ## TODO: DEAL WITH UNDERSCORE!!!
                evcs += '))\n'
            if constr.Consts:
                evcs += ('(C%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(constr.Consts)  ## TODO: DEAL WITH UNDERSCORE!!!
                evcs += '))\n'
            if constr.Arithms or constr.Unary:  # include shifts
                evcs += ('(Arithm%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(['(%s E%d E%d)' % (op, width, width) for op in constr.Arithms] + \
                                 ['(%s E%d)' % (op, width) for op in constr.Unary])
                evcs += '))\n'
            if constr.Concats:
                evcs += ('(Concat%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(['(concat' + (' E%d E%d' % (w1, w2)) + ')' for w1, w2 in constr.Concats])
                evcs += '))\n'
            if constr.Extracts:
                evcs += ('(Extract%d' % width) + ' ' + tp + ' ('
                # need to define functions
                exts = []
                for inw, h, l in constr.Extracts:  # whether it is necessary remains a question
                    exts.append('((_ extract {h} {l}) E{inw})'.format(h=h, l=l, inw=inw))
                evcs += ' '.join(exts)
                evcs += '))\n'
            if constr.Rotates:
                evcs += ('(Rotate%d' % width) + ' ' + tp + ' ('
                exts = []
                for op, param in constr.Rotates:  # whether it is necessary remains a question
                    exts.append('((_ {op} {p}) E{w})'.format(op=op, p=param, w=width))
                evcs += ' '.join(exts)
                evcs += '))\n'
            if constr.Exts:
                evcs += ('(Ext%d' % width) + ' ' + tp + ' ('
                exts = []
                for op, param, inw in constr.Exts:  # whether it is necessary remains a question
                    exts.append('((_ {op} {p}) E{w})'.format(op=op, p=param, w=width))
                evcs += ' '.join(exts)
                evcs += '))\n'

        nt_stx = ' '.join(['(%s %s)' % (n, t) for n, t in nonterminals])
        return comps, evcs, nt_stx

    def _remove_unused_width(self):
        start_set = set([])
        use_map = {}
        for width, constr in self.LangConstructs.items():
            if len(constr.Consts) > 0 or len(constr.Vars) > 0:
                start_set.add(width)
            use_map[width] = set([width])
            for _, _, inw in constr.Exts:
                use_map[width].add(inw)
            for inw, _, _ in constr.Extracts:  # whether it is necessary remains a question
                use_map[width].add(inw)
            for w1, w2 in constr.Concats:
                use_map[width].add(w1)
                use_map[width].add(w2)
        all_width = list(self.LangConstructs.keys())
        g = GraphReach(
            nodes=all_width,
            use_map=use_map, concrete_vals=start_set)
        used_width = g.compute_reach()

        for width in all_width:
            if width not in used_width:
                del self.LangConstructs[width]


# ----------------------------------------------
# let's do some test on the generation

def test():
    pass


if __name__ == '__main__':
    test()

# ~/cvc-installs/latest/bin/cvc4 --lang=sygus2 idx.sygus
