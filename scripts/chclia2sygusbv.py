"""
CHC(LIA) to SYGUS(BV)
"""
import os
import z3
from typing import List
from efmc.frontends.mini_sygus_parser import SyGusInVParser, parse_sexpression
from efmc.frontends.chc_parser import CHCParser, ground_quantifier

g_bitvector_width = 32
g_bitvector_signedness = "signed"


def rep_operand(op: str) -> str:
    if g_bitvector_signedness == "signed":
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     "div": "bvudiv",
                     ">=": "bvsge", "<=": "bvsle", ">": "bvsgt", "<": "bvslt"}
    else:
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvurem",
                     "div": "bvsdiv",
                     ">=": "bvuge", "<=": "bvule", ">": "bvugt", "<": "bvult"}

    if op in rep_rules:
        return rep_rules[op]
    return op


def to_bv_sexpr_misc(line: List[str]):
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
            # replace int with bv
            if isinstance(element, int):
                res.append("(_ bv{} {})".format(element, g_bitvector_width))
            else:
                res.append(str(element))
    res.append(")")
    return res


def ira2bv(tt: str) -> str:
    return " ".join(to_bv_sexpr_misc(parse_sexpression(tt)))


def chclia2sygusbv(tt):
    # ss = SyGusInVParser(tt, to_real=False)
    ss = CHCParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    # print(all_vars, init, trans, post)
    # print("all_vars = " , all_vars)
    # print("init = " , init)
    # print("trans = ", trans)
    # print("post = " , post)
    # [x, y, x!, y!], Pre(x, y), T(x, y, x!, y!), Post(x, y)
    #  NOTE: I assume that variables in all_vars are "sorted".
    init_vars = all_vars[0: int(len(all_vars) / 2)]
    trans_vars = all_vars[int(len(all_vars) / 2):]
    print("init_vars = " , init_vars)
    print("trans_vars = " , trans_vars)
    # For BV
    # (declare-fun inv ((_ BitVec 8)) Bool)
    bv_inv_sig = "(synth-inv inv_fun ("
    for init_var in init_vars:
        # bv_inv_sig += "(_ BitVec {}) ".format(g_bitvector_width)
        bv_inv_sig += "({} {})".format(str(init_var), z3.BitVec(str(init_var), g_bitvector_width).sort().sexpr())
    bv_inv_sig += "))\n\n"

    bv_fml_str = "(set-logic BV)\n\n"
    bv_fml_str += bv_inv_sig
    # print(bv_fml_str)
    # init cnt
    bv_init_vars_sig = []
    bv_init_vars = []
    for var in init_vars:
        bv_init_vars_sig.append("({} {})".format(str(var), z3.BitVec(str(var), g_bitvector_width).sort().sexpr()))
        bv_init_vars.append(str(var))
    # print(bv_init_vars_sig)
    # print(init)
    bv_init_cnt = "(define-fun pre_fun ({}) Bool\n"  \
                  "       {})\n".format(" ".join(bv_init_vars_sig),
                                                      ira2bv(init.sexpr()))
    # print(bv_init_cnt)
    bv_fml_str += bv_init_cnt
    # print(bv_fml_str)
    # trans cnt
    bv_all_vars_sig = []
    bv_all_vars = []
    bv_trans_vars = [str(var) for var in trans_vars]

    for var in all_vars:
        bv_all_vars_sig.append("({} {})".format(str(var), z3.BitVec(str(var), g_bitvector_width).sort().sexpr()))
        bv_all_vars.append(str(var))

    bv_trans_cnt = "(define-fun trans_fun ({}) Bool\n"  \
                  "       {})\n".format(" ".join(bv_all_vars_sig),
                                                      ira2bv(trans.sexpr()))
    # print(bv_trans_cnt)
    # print(bv_trans_cnt)
    bv_fml_str += bv_trans_cnt

    # Post cnt
    bv_post_cnt = "(define-fun post_fun ({}) Bool\n"  \
                  "       {})\n\n".format(" ".join(bv_init_vars_sig),
                                                      ira2bv(post.sexpr()))

    # print(bv_post_cnt)
    bv_fml_str += bv_post_cnt
    bv_fml_str += "(inv-constraint inv_fun pre_fun trans_fun post_fun)\n\n"
    bv_fml_str += "(check-synth)\n\n"
    # print(bv_fml_str)
    return bv_fml_str


def test_main():
    tt = """
        (set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((y0 Int) (x0 Int)) (=> (and (= x0 0) (= y0 5000)) (inv x0 y0))))
(assert (forall ((y1 Int) (x1 Int) (y0 Int) (x0 Int))
  (let ((a!1 (and (inv x0 y0)
                  (= x1 (+ x0 1))
                  (= y1 (ite (>= x0 5000) (+ y0 1) y0)))))
    (=> a!1 (inv x1 y1)))))
(assert (forall ((x0 Int) (y0 Int))
  (=> (and (inv x0 y0) (= x0 10000) (not (= y0 x0))) false)))
(check-sat)"""

    # print(sygus2chc(tt))
    # new_ctx = z3.Context()
    fml_str = chclia2sygusbv(tt)

    print(fml_str)
    # print(fml_str)


def process_file(filename: str, target_dir: str):

    print("Processing ", filename)
    try:
        with open(filename, "r") as f:
            content = f.read()
            fml_str = chclia2sygusbv(content)
            filename_base = os.path.basename(filename)
            # new_file_name = target_dir + filename_base + ".smt2"
            new_file_name = target_dir + filename_base + \
                            "_{0}bits_{1}".format(str(g_bitvector_width), g_bitvector_signedness) + ".sl"

            with open(new_file_name, "w") as new_f:
                print("Writing to ", new_file_name)
                new_f.write(fml_str)
                new_f.close()

            f.close()
    except Exception as ex:
        print(ex)
        if "mod" in str(ex):
            os.remove(filename)


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
    # test_main()
    # exit(0)
    from pathlib import Path

    project_root_dir = str(Path(__file__).parent.parent)
    print(project_root_dir)

    target_dir = project_root_dir + "/tmp_chclia2sygus/"
    process_folder(project_root_dir + "/benchmarks/chc/lia/multi-phase/multi-phase_unsafe", target_dir)
