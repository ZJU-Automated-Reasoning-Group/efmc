"""
Converting SyGuS(Inv) benchmarks to CHC instances

    sygus2chc: preserves the variable types

    sygus2chcbv: translate to bv semantics (not semantic-preserving!)
"""
import os

# from ..efsmt.frontends.mini_sygus_parser import test_main
import z3
from z3.z3util import get_vars

from efmc.frontends.mini_sygus_parser import SyGusInVParser, parse

g_bitvector_width = 8
g_bitvector_signedness = "unsigned"


def sygus2chc(tt: str) -> str:
    # ss = SyGusInVParser("\n".join(tt_arr), to_real=False)
    ss = SyGusInVParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    init_vars = get_vars(init)
    trans_vars = list(set(all_vars).difference(set(init_vars)))

    s = z3.SolverFor("HORN")
    inv_sig = "Function(\'inv\', "
    for _ in range(len(init_vars)): inv_sig += "IntSort(),"
    inv_sig += "BoolSort())"
    inv = eval(inv_sig)

    # print(z3.ForAll(init_vars, z3.Implies(init, inv(init_vars))).sexpr())

    s.add(z3.ForAll(init_vars, z3.Implies(init,
                                          inv(init_vars))))

    s.add(z3.ForAll(all_vars, z3.Implies(z3.And(inv(init_vars), trans),
                                         inv(trans_vars))))

    s.add(z3.ForAll(init_vars, z3.Implies(inv(init_vars),
                                          post)))
    # print(input_to_list(tttt))

    fml_str = "(set-logic HORN)\n"
    fml_str += "\n".join(s.to_smt2().split("\n")[2:])
    return fml_str


def rep_operand(op: str) -> str:
    if g_bitvector_signedness == "signed":
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     ">=": "bvsge", "<=": "bvsle", ">": "bvsgt", "<": "bvslt"}
    else:
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     ">=": "bvuge", "<=": "bvule", ">": "bvugt", "<": "bvult"}

    if op in rep_rules:
        return rep_rules[op]
    return op


def to_bv_sexpr_misc(line: [str]):
    """
    This is used for converting LIRA expressions to BV
    E.g.,
    ['and', ['=', 'x', 1], ['=', 'y', 1]]
    ['and', ['=', 'x!', ['+', 'x', 'y']], ['=', 'y!', ['+', 'x', 'y']]]
    """
    res = ["("]
    if not isinstance(line[0], list):
        if line[0] == '-' and len(line) == 2 and (not isinstance(line[1], list)):  # ['-', 50]
            """
            Consider  x == -50, i.e., ['=', 'x', ['-', 50]]
            https://stackoverflow.com/questions/37044372/how-to-present-negative-number-in-bitvector
            This is usually done via two's complement encoding. The short version is,
                   -x = flip(x) + 1
                   where flip(x) simply flips all the bits in x. NOTE: flip is  (bvnot x) in SMT-LIB

             According to the above discussion,  ['-', 50] should be converted to
                      ['bvadd', 1, [bvnot', 50]]
            """
            if isinstance(line[1], int):
                var = '(_ bv{} {})'.format(line[1], g_bitvector_width)
            else:
                var = line[1]
            new_line = ['bvadd', '(_ bv1 {})'.format(g_bitvector_width), ['bvnot', var]]
        else:
            new_line = [rep_operand(line[0])]
            new_line += line[1:]
    else:
        new_line = line

    for element in new_line:
        if isinstance(element, list):
            # rep operand
            if not isinstance(element[0], list):
                # handling cases like x = -50 (same as above)
                if element[0] == '-' and len(element) == 2 and (not isinstance(element[1], list)):  # ['-', 50]
                    if isinstance(element[1], int):
                        var = '(_ bv{} {})'.format(element[1], g_bitvector_width)
                    else:
                        var = element[1]
                    new_element = ['bvadd', '(_ bv1 {})'.format(g_bitvector_width), ['bvnot', var]]
                else:
                    new_element = [rep_operand(element[0])]
                    new_element += element[1:]
            else:
                new_element = element

            for exp in to_bv_sexpr_misc(new_element):
                res.append(exp)
        else:
            if isinstance(element, int):
                res.append("(_ bv{} {})".format(element, g_bitvector_width))
            else:
                res.append(str(element))
    res.append(")")
    return res


def ira2bv(tt: str) -> str:
    return " ".join(to_bv_sexpr_misc(parse(tt)))


def sygus2chcbv(tt):
    """
    FIXME: how to convert constants...
    """
    # chc_lira_str = sygus2chc(tt)
    ss = SyGusInVParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    #  NOTE: I assume that variables in all_vars are "sorted".
    init_vars = all_vars[0: int(len(all_vars) / 2)]
    trans_vars = all_vars[int(len(all_vars) / 2):]
    # init_vars = get_vars(init) # not good?
    # For BV
    # (declare-fun inv ((_ BitVec 8)) Bool)
    bv_inv_sig = "(declare-fun inv ("
    for _ in range(len(init_vars)):
        bv_inv_sig += "(_ BitVec {}) ".format(g_bitvector_width)
    bv_inv_sig += ") Bool)\n"

    bv_fml_str = "(set-logic HORN)\n"
    bv_fml_str += bv_inv_sig

    # init cnt
    bv_init_vars_sig = []
    bv_init_vars = []
    for var in init_vars:
        bv_init_vars_sig.append("({} {})".format(str(var), z3.BitVec(str(var), g_bitvector_width).sort().sexpr()))
        bv_init_vars.append(str(var))

    # print(init)

    bv_init_cnt = "(assert (forall ({}) \n " \
                  "      (=> {} (inv {}))))\n".format(" ".join(bv_init_vars_sig),
                                                      ira2bv(init.sexpr()),
                                                      " ".join(bv_init_vars))
    # print(bv_init_cnt)
    bv_fml_str += bv_init_cnt

    # trans cnt
    bv_all_vars_sig = []
    bv_all_vars = []
    bv_trans_vars = [str(var) for var in trans_vars]

    for var in all_vars:
        bv_all_vars_sig.append("({} {})".format(str(var), z3.BitVec(str(var), g_bitvector_width).sort().sexpr()))
        bv_all_vars.append(str(var))

    bv_trans_cnt = "(assert (forall ({}) \n " \
                   "      (=> (and (inv {}) {}) (inv {}))))\n".format(" ".join(bv_all_vars_sig),
                                                                      " ".join(bv_init_vars),
                                                                      ira2bv(trans.sexpr()),
                                                                      " ".join(bv_trans_vars))

    # print(bv_trans_cnt)
    bv_fml_str += bv_trans_cnt

    # Post cnt
    bv_post_cnt = "(assert (forall ({}) \n " \
                  "      (=> (inv {}) {})))\n".format(" ".join(bv_init_vars_sig),
                                                      " ".join(bv_init_vars),
                                                      ira2bv(post.sexpr())
                                                      )

    # print(bv_post_cnt)
    bv_fml_str += bv_post_cnt
    bv_fml_str += "(check-sat)\n"
    return bv_fml_str


def test_main():
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

    # print(sygus2chc(tt))
    new_ctx = z3.Context()
    fml_str = sygus2chcbv(tt)
    print(fml_str)
    s = z3.Solver(ctx=new_ctx)
    s.from_string(fml_str)
    print(s)


def process_file(filename):
    print("Processing ", filename)
    with open(filename, "r") as f:
        content = f.read()
        fml_str = sygus2chcbv(content)
        # print(fml_str)
        # s = SolverFor("HORN")
        # s.add(And(parse_smt2_string(fml_str)))
        # s.set("timeout", 1000)
        # print(s.to_smt2())
        # print(s.check())
        # print("XXXXXXX")
        base = os.path.basename(filename)
        new_file_name = "/Users/prism/Work/eldarica-bin/tests/sygus/" + base + ".smt2"
        with open(new_file_name, "w") as new_f:
            new_f.write(fml_str)
            new_f.close()

        f.close()


def process_folder(path: str):
    flist = []  # path to smtlib2 files
    for root, dirs, files in os.walk(path):
        for fname in files:
            tt = os.path.splitext(fname)[1]
            if tt == '.smt2' or tt == '.sl':
                flist.append(os.path.join(root, fname))
    for filename in flist:
        process_file(filename)


if __name__ == '__main__':
    # tt = "(and (<= x! (+ x y)) (< y! (+ x y)))"
    # print(ira2bv(tt))
    # test_main()
    # process_file("/Users/prism/Work/efmc/benchmarks/sygus-inv/LIA/2017.ASE_FiB/minor3.sl")
    process_folder("/Users/prism/Work/efmc/benchmarks/sygus-inv/LIA/2017.ASE_FiB")
