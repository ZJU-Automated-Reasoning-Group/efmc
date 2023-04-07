from pathlib import Path

project_root_dir = str(Path(__file__).parent.parent.parent.parent.parent)
z3_exec = project_root_dir + "/bin_solvers/z3"
cvc5_exec = project_root_dir + "/bin_solvers/cvc5"

caqe_exec = project_root_dir + "/bin_solvers/caqe"

g_bin_solver_timeout = 30

g_efsmt_args = None