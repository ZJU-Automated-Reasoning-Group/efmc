# coding: utf-8

"""
NOTE: I only it for SyGuS inv. It could be used for PBE

To keep this file independent, I do not important other files in this project.
"""
import z3

# Being explicit about Types
Symbol = str
Number = (int, float)
Atom = (Symbol, Number)
List = list
Expr = (Atom, List)


def input_to_list(string: str) -> [str]:
    """
    Parse a .sl file into a list of S-Expressions.
    """
    n: int = 0
    result: [str] = []
    s: str = ""
    for c in string:
        if c == "(":
            n += 1
        if c == ")":
            n -= 1
        if c != "\n":
            s += c
        if n == 0 and s != "":
            result.append(s)
            s = ""
    return result


def tokenize(chars: str) -> list:
    """Convert a string of characters into a list of tokens."""
    return chars.replace('(', ' ( ').replace(')', ' ) ').replace('" "', 'space').split()


def parse(program: str) -> Expr:
    """Read an S-expression from a string."""
    return read_from_tokens(tokenize(program))


def read_from_tokens(tokens: list) -> Expr:
    """Read an expression from a sequence of tokens."""
    if len(tokens) == 0:
        return
        # raise SyntaxError('unexpected EOF') # is this OK?
    token = tokens.pop(0)
    if token == '(':
        L = []
        while tokens[0] != ')':
            L.append(read_from_tokens(tokens))
        tokens.pop(0)  # pop off ')'
        return L
    elif token == ')':
        raise SyntaxError('unexpected )')
    else:
        return atom(token)


def atom(token: str) -> Atom:
    """Numbers become numbers; every other token is a symbol."""
    try:
        return int(token)
    except ValueError:
        try:
            return float(token)
        except ValueError:
            return Symbol(token)


def get_start(cmd) -> str:
    assert (cmd[0] == "synth-fun")
    return cmd[4][0]


def get_nonterminals(cmd):
    nonterms = set()
    type_dict = {}
    assert (cmd[0] == "synth-fun")
    for elem in cmd[4]:
        nt = elem[0]
        typ = elem[1]
        nonterms.add(nt)
        type_dict[nt] = typ
    return nonterms, type_dict


def get_terms_prods(cmd):
    terminals = set()
    productions = {}
    for nonterm_list in cmd[5]:
        non_term = nonterm_list[0]
        product = []
        for t in nonterm_list[2]:
            # Non-terminals that go with a production
            nts = []

            if isinstance(t, list):
                # gets a terminal from the input, e.g., `"+"`
                term = t[0]
                # List of potential non-terminal children, e.g, `["I", "I"]` for `"+"`
                nts += t[1:]
            else:
                term = t

            if isinstance(term, list):
                term = tuple(term)
            terminals.add(term)

            product.append((term, nts))
        productions[non_term] = product
    return terminals, productions


def get_grammar(lines: [str]):
    s_exprs = []
    for line in lines:
        s_exprs.append(parse(line))
    for s in s_exprs:
        if s[0] == "synth-fun":
            start_sym = get_start(s)
            nonterminals = get_nonterminals(s)
            terminals, productions = get_terms_prods(s)
            return nonterminals, terminals, productions, start_sym


pre_func_names = ["pre_fun", "PreF", "pre-f"]
trans_func_names = ["trans_fun", "TransF", "trans-f"]
post_func_names = ["post_fun", "PostF", "post-f"]


class SyGusInVParser:

    def __init__(self, inputs: str, to_real: bool):
        self.to_real = to_real
        self.logic = None
        self.inv_vars = []
        self.all_vars = []
        self.inv_arity = 0
        self.pre_fun_body = ""
        self.trans_fun_body = ""
        self.post_fun_body = ""

        self.init_symbols(inputs)

    def to_sexpr_misc(self, lines: [str]):
        """
        E.g.,
        ['and', ['=', 'x', 1], ['=', 'y', 1]]
        ['and', ['=', 'x!', ['+', 'x', 'y']], ['=', 'y!', ['+', 'x', 'y']]]
        """
        res = ["("]
        for element in lines:
            if isinstance(element, list):
                for e in self.to_sexpr_misc(element):
                    res.append(e)
            else:
                if isinstance(element, int) and self.to_real:
                    element = str(element) + ".0"
                res.append(str(element))
        res.append(")")
        return res

    def to_sexpr(self, lines: [str]):
        return " ".join(self.to_sexpr_misc(lines))

    def init_symbols(self, inputs: str):
        """
        TODO: this is not robust (as an sexpr can have several lines)
        """
        lines = input_to_list(inputs)
        for line in lines:
            slist = parse(line)
            # print(slist)
            if isinstance(slist, List):
                cmd_name = slist[0]
                if cmd_name == "set-logic":
                    self.logic = slist[1]
                elif cmd_name == "synth-inv":
                    self.inv_arity = len(slist[2])
                elif cmd_name == "define-fun":
                    self.process_func(slist)
                elif cmd_name == "inv-constraint":
                    break
                else:
                    break
        # print(self.pre_fun_body)
        # print(self.trans_fun_body)
        # print(self.post_fun_body)

    def process_func(self, slist):
        # print(slist)
        assert len(slist) >= 5
        func_name = slist[1]
        if func_name in pre_func_names:
            self.pre_fun_body = self.to_sexpr(slist[4])
            self.inv_vars = slist[2]
        elif func_name in trans_func_names:
            self.trans_fun_body = self.to_sexpr(slist[4])
            self.all_vars = slist[2]
        elif func_name in post_func_names:
            self.post_fun_body = self.to_sexpr(slist[4])
        else:
            # print("Function name not recognized!:", func_name)
            raise AssertionError("Function name not recognized!: {}".format(func_name))

    def get_transition_system(self):
        """
        Return the format of our trivial transition system
        """
        from z3.z3util import get_vars
        init_cnts = []
        trans_cnts = []
        post_cnts = []
        for var in self.all_vars:
            vname, vtype = var[0], var[1]
            # print(vname, vtype)
            if isinstance(vtype, List):
                # E.g., ['Array', 'Int', 'Int']
                final_type = "({})".format(" ".join(vtype))
            else:
                # FIXME: to test abstract domains, we may cast Int types to Real
                # FIXME: but casting here is not very elegant
                if self.to_real and vtype != "Real":
                    final_type = "Real"
                else:
                    final_type = vtype

            init_cnts.append("(declare-const {} {})".format(vname, final_type))
            trans_cnts.append("(declare-const {} {})".format(vname, final_type))
            post_cnts.append("(declare-const {} {})".format(vname, final_type))

        init_cnts.append("(assert {})".format(self.pre_fun_body))
        trans_cnts.append("(assert {})".format(self.trans_fun_body))
        post_cnts.append("(assert {})".format(self.post_fun_body))

        # print("\n".join(init_cnts))
        # print("\n".join(trans_cnts))
        # print("\n".join(post_cnts))

        init = z3.parse_smt2_string("\n".join(init_cnts))[0]
        trans = z3.parse_smt2_string("\n".join(trans_cnts))[0]
        post = z3.parse_smt2_string("\n".join(post_cnts))[0]

        # a dirty trick to keep order?
        # TODO: does th following functions preseve some order?
        # Is the order necessary?

        # it's possible that some variables in self.all_vars are not used
        z3_vars = get_vars(z3.And(init, trans, post))
        z3_vars_names = [str(var) for var in z3_vars]
        temp_cnts = []
        for var_sig in self.all_vars:  # ['i', 'Int']
            if var_sig[0] not in z3_vars_names:
                if self.to_real:
                    temp_cnts.append(z3.Real(var_sig[0]) == z3.RealVal(1.0))
                else:
                    temp_cnts.append(z3.Int(var_sig[0]) == z3.IntVal(1))
        # get_vars(z3.And(z3.And(temp_cnts), z3.And(init, trans, post)))

        all_vars = []
        for var_sig in self.all_vars:  # ['i', 'Int']
            if self.to_real:
                all_vars.append(z3.Real(var_sig[0]))
            else:
                all_vars.append(z3.Int(var_sig[0]))
        # print(all_vars)
        # print(self.all_vars)
        return all_vars, init, trans, post


def test_parser():
    tt = [
        ";\n",
        "(set-logic LIA)",
        " (synth-inv inv_fun ((x Int) (y Int)))\n",
        "(define-fun pre_fun ((x Int) (y Int)) Bool (and (= x 1) (= y 1))) ",
        "(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool (and (= x! (+ x y)) (= y! (+ x y))))",
        "(define-fun post_fun ((x Int) (y Int)) Bool (>= y 1))",
        "(inv-constraint inv_fun pre_fun trans_fun post_fun)",
        "(check-synth)"
        "; xxx"]

    alia = """(set-logic ALIA)
(synth-inv inv_fun ((x (Array Int Int)) (y Int) (n Int)))
(define-fun pre_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (and (>= n 0) (and (= n (select x 0)) (= y 0))))
(define-fun trans_fun ((x (Array Int Int)) (y Int) (n Int) (x! (Array Int Int)) (y! Int) (n! Int)) Bool
    (and (> (select x 0) 0) (and (= n! n) (and (= y! (+ y 1)) (= x! (store x 0 (- (select x 0) 1)))))))
(define-fun post_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (or (> (select x 0) 0) (= n (+ (select x 0) y))))
(inv-constraint inv_fun pre_fun trans_fun post_fun)
(check-synth)
        """

    str_inv = """
    (synth-inv inv_fun ((x (Array Int Int)) (y Int) (n Int)))
    (define-fun pre_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
        (and (>= n 0) (and (= n (select x 0)) (= y 0))))
    (define-fun trans_fun ((x (Array Int Int)) (y Int) (n Int) (x! (Array Int Int)) (y! Int) (n! Int)) Bool
        (and (> (select x 0) 0) (and (= n! n) (and (= y! (+ y 1)) (= x! (store x 0 (- (select x 0) 1)))))))
    (define-fun post_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
        (or (> (select x 0) 0) (= n (+ (select x 0) y))))
    (inv-constraint inv_fun pre_fun trans_fun post_fun)
    (check-synth)
            """
    # ss = SyGusInVParser("\n".join(tt_arr), to_real=False)
    ss = SyGusInVParser(alia, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    print(init, "\n", trans, "\n", post)
    # print(input_to_list(tttt))


if __name__ == '__main__':
    test_parser()