"""
CHC(LIA) to CHC(BV)
"""
import os
from typing import List

import z3

from efmc.frontends.mini_sygus_parser import SyGusInVParser, parse_sexpression
from efmc.frontends.chc_parser import CHCParser, ground_quantifier
from efmc.utils.z3_expr_utils import get_variables

g_bitvector_width = 64
g_bitvector_signedness = "signed"


def rep_operand(op: str) -> str:
    """
    Replace the operand with the corresponding BV operator.
    """
    if g_bitvector_signedness == "signed":
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvsdiv",
                     "div": "bvsdiv",
                     ">=": "bvsge", "<=": "bvsle", ">": "bvsgt", "<": "bvslt"}
    else:
        rep_rules = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "%": "bvurem",
                     "div": "bvudiv",
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


def chclia2chcbv(tt):
    # ss = SyGusInVParser(tt, to_real=False)
    ss = CHCParser(tt, to_real=False)
    all_vars, init, trans, post = ss.get_transition_system()
    # print(all_vars, init, trans, post)
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

    # In the multi-phase benchmark, x1, y1, .. are used to denote
    # prime variables. However, our transition system will only regard
    # variables named x!, y!, .. as prime variables
    fmls = z3.parse_smt2_string(bv_fml_str)
    assert len(fmls) == 3
    trans_fml = fmls[1]
    trans_body, trans_vars_list = ground_quantifier(trans_fml)
    mappings = []  # for replacing the var names
    # [(x0, x), (y0, y), (x1, x!), (y1, y!)]
    for var in trans_vars_list:
        if str(var).endswith("1"):
            new_var_name = str(var)[:-1] + "!"
        elif str(var).endswith("0"):
            new_var_name = str(var)[:-1]
        new_var = z3.BitVec(new_var_name, var.sort())
        mappings.append((var, new_var))
    # replace the variables in init, trans, post with new var names
    new_init_qf = z3.substitute(ground_quantifier(fmls[0])[0], mappings)
    new_trans_qf = z3.substitute(trans_body, mappings)
    new_post_qf = z3.substitute(ground_quantifier(fmls[2])[0], mappings)

    # 2. Second, create the quantified formula
    sol = z3.Solver()
    new_init_post_vars_list = get_variables(new_post_qf)
    new_trans_vars_list = get_variables(new_trans_qf)

    sol.add(z3.ForAll(new_init_post_vars_list, new_init_qf))  # init
    sol.add(z3.ForAll(new_trans_vars_list, new_trans_qf))
    sol.add(z3.ForAll(new_init_post_vars_list, new_post_qf))
    final_fml_str = "(set-logic HORN)\n"
    final_fml_str += sol.sexpr()
    final_fml_str += "(check-sat)\n"

    return final_fml_str


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

    file = "/regressions/chc/lia/multi-phase/multi-phase_safe/s_split_27.smt2"
    with open(file, "r") as f:
        content = f.read()
        fml_str = chclia2chcbv(content)
        print(fml_str)
        # print(fml_str)

def process_file(filename: str, target_dir: str):
    print("Processing ", filename)
    try:
        with open(filename, "r") as f:
            content = f.read()
            fml_str = chclia2chcbv(content)
            filename_base = os.path.basename(filename)
            # new_file_name = target_dir + filename_base + ".smt2"
            new_file_name = target_dir + filename_base + "unsafe" + \
                            "_{0}bits_{1}".format(str(g_bitvector_width), g_bitvector_signedness) + ".smt2"

            with open(new_file_name, "w") as new_f:
                print("Writing to ", new_file_name)
                new_f.write(fml_str)
                new_f.close()

            f.close()
    except Exception as ex:
        print(ex)
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

    target_dir = project_root_dir + "/tmp_files/"
    process_folder(project_root_dir + "/benchmarks/chc/lia/multi-phase/multi-phase_unsafe", target_dir)
