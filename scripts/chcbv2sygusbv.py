# CHC to SyGuS

from efmc.frontends import parse_sygus, parse_chc
from efmc.sts import TransitionSystem


def chc2sygus(file_name: str):
    """Solve a CHC file
    :param file_name: the CHC file
    :param prover: strategy
    """
    all_vars, init, trans, post = parse_chc(file_name, to_real_type=False)
    print("Finish parsing CHC file")
    sts = TransitionSystem()
    sts.from_z3_cnts([all_vars, init, trans, post])

    print(sts)

def demo():
    fml = """
    (set-logic HORN)
(declare-fun inv ((_ BitVec 32) (_ BitVec 32) ) Bool)
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> ( = x ( bvadd (_ bv1 32) ( bvnot (_ bv50 32) ) ) ) (inv x y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (x! (_ BitVec 32)) (y! (_ BitVec 32))) 
       (=> (and (inv x y) ( or ( and ( bvslt x (_ bv0 32) ) ( = x! ( bvadd x y ) ) ( = y! ( bvadd y (_ bv1 32) ) ) ) ( and ( bvsge x (_ bv0 32) ) ( = x! x ) ( = y! y ) ) )) (inv x! y!))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) 
       (=> (inv x y) ( => ( not ( bvslt x (_ bv0 32) ) ) ( bvsge y (_ bv0 32) ) ))))
(check-sat)
    """
    print(fml)

if __name__ == '__main__':
    # tt = "(and (<= x! (+ x y)) (< y! (+ x y)))"
    # print(ira2bv(tt))
    # test_main()
    from pathlib import Path
    project_root_dir = str(Path(__file__).parent.parent)
    chc2sygus(project_root_dir + "/tmp_files/fib_04.sl_32bits_signed.smt2")

