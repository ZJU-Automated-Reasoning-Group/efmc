"""
Converting SyGuS(Inv) benchmarks to CHC instances

    sygus2chc: preserves the variable types
      - E.g., from SyGuS(LIA) to CHC(LIA)

    sygus2chcbv: translate to bv semantics (not semantic-preserving!)
      - E.g., from SyGuS(LIA) to CHC(BV)

"""

import os
import z3
from efmc.frontends.mini_sygus_parser import SyGusInVParser, parse_sexpression

g_bitvector_width = 64
g_bitvector_signedness = "signed"


def sygus2chc(tt: str) -> str:
    # ss = SyGusInVParser("\n".join(tt_arr), to_real=False)
    from z3 import Function, IntSort, BoolSort
    # chc_lira_str = sygus2chc(tt)
    ss = SyGusInVParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    #  NOTE: I assume that variables in all_vars are "sorted".
    init_vars = all_vars[0: int(len(all_vars) / 2)]
    trans_vars = all_vars[int(len(all_vars) / 2):]
    # print("all vars: ", all_vars)
    # print("init vars: ", init_vars)
    # init_vars = get_vars(init) # not good?
    inv_sig = "(declare-fun inv ("
    for _ in range(len(init_vars)):
        inv_sig += "Int "
    inv_sig += ") Bool)\n"

    fml_str = "(set-logic HORN)\n"
    fml_str += inv_sig

    # init cnt
    init_vars_sig = []
    ira_init_vars = []
    for var in init_vars:
        init_vars_sig.append("({0} {1})".format(str(var), "Int"))
        ira_init_vars.append(str(var))
    print("init_vars: ", init_vars)
    init_cnt = "(assert (forall ({}) \n " \
               "      (=> {} (inv {}))))\n".format(" ".join(init_vars_sig),
                                                   init.sexpr(),
                                                   " ".join(ira_init_vars))
    # print(bv_init_cnt)
    fml_str += init_cnt

    # trans cnt
    all_vars_sig = []
    trans_vars = [str(var) for var in trans_vars]
    ira_all_vars = []
    for var in all_vars:
        all_vars_sig.append("({} {})".format(str(var), "Int"))
        ira_all_vars.append(str(var))
    # print("all vars sig: ", all_vars_sig)

    bv_trans_cnt = "(assert (forall ({0}) \n " \
                   "      (=> (and (inv {1}) {2}) (inv {3}))))\n".format(" ".join(all_vars_sig),
                                                                         " ".join(ira_init_vars),
                                                                         trans.sexpr(),
                                                                         " ".join(trans_vars))

    # print(bv_trans_cnt)
    fml_str += bv_trans_cnt

    # Post cnt
    post_cnt = "(assert (forall ({}) \n " \
                  "      (=> (inv {}) {})))\n".format(" ".join(init_vars_sig),
                                                      " ".join(ira_init_vars),
                                                      post.sexpr()
                                                      )

    # print(bv_post_cnt)
    fml_str += post_cnt
    fml_str += "(check-sat)\n"
    return fml_str


def rep_operand(op: str) -> str:
    if g_bitvector_signedness == "signed":
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     "div": "bvsdiv",
                     ">=": "bvsge", "<=": "bvsle", ">": "bvsgt", "<": "bvslt"}
    else:
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     "div": "bvudiv",
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
    return " ".join(to_bv_sexpr_misc(parse_sexpression(tt)))


def sygus2chcbv(tt):
    """
    FIXME: how to convert constants...
    """
    # chc_lira_str = sygus2chc(tt)
    ss = SyGusInVParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    # [x, y, x!, y!], Pre(x, y), T(x, y, x!, y!), Post(x, y)
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
                                                      # init: z3.ExprRef
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
                                                                      # trans: z3.ExprRef
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


def process_file(filename: str, target_dir: str):
    print("Processing ", filename)
    with open(filename, "r") as f:
        content = f.read()
        fml_str = sygus2chcbv(content)
        # fml_str = sygus2chc(content)
        # print(fml_str)
        # s = SolverFor("HORN")
        # s.add(And(parse_smt2_string(fml_str)))
        # s.set("timeout", 1000)
        # print(s.to_smt2())
        # print(s.check())
        filename_base = os.path.basename(filename)
        # new_file_name = target_dir + filename_base + ".smt2"
        new_file_name = target_dir + filename_base + \
                        "_{0}bits_{1}".format(str(g_bitvector_width), g_bitvector_signedness) + ".smt2"

        with open(new_file_name, "w") as new_f:
            print("Writing to ", new_file_name)
            new_f.write(fml_str)
            new_f.close()

        f.close()

def process_folder(path: str, target_dir: str):
    flist = []  # path to smtlib2 files
    for root, dirs, files in os.walk(path):
        for fname in files:
            tt = os.path.splitext(fname)[1]
            if tt == '.smt2' or tt == '.sl':
                flist.append(os.path.join(root, fname))
    for filename in flist:
        process_file(filename, target_dir)


if __name__ == '__main__':
    # tt = "(and (<= x! (+ x y)) (< y! (+ x y)))"
    # print(ira2bv(tt))
    # test_main()
    from pathlib import Path
    project_root_dir = str(Path(__file__).parent.parent)
    print(project_root_dir)

    target_dir = project_root_dir + "/tmp_files/"
    # print(project_root_dir + "/benchmarks/sygus-inv/LIA/2017.ASE_FiB")
    process_folder(project_root_dir + "/benchmarks/sygus-inv/NIA/2018.CHI_InvGame", target_dir)
