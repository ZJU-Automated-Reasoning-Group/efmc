import z3

from efmc.engines.abduction.abductor.mistral_z3 import MSASolver


def dillig_abduce(pre_cond: z3.BoolRef, post_cond: z3.BoolRef) -> z3.ExprRef:
    """
    Dillig-style abduction (which is very expensive)

    Essentially, MSA + qe_abduce??

    a, b, c, d = Ints('a b c d')
    fml = Or(And(a == 3, b == 3), And(a == 1, b == 1, c == 1, d == 1))
    ms = MSASolver()
    ms.init_from_formula(fml)
    print(ms.find_small_model())  # a = 3, b = 3
    """
    msa = MSASolver()
    return post_cond
