from pathlib import Path


class EFMCConfig:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super(EFMCConfig, cls).__new__(cls)
            cls._instance._initialize()
        return cls._instance

    def _initialize(self):
        # Should we try to find the executables automatically? (e.g., from the system path?)
        self.project_root_dir = str(Path(__file__).parent.parent)
        self.z3_exec = self.project_root_dir + "/bin_solvers/bin/z3"
        self.cvc5_exec = self.project_root_dir + "/bin_solvers/bin/cvc5"
        self.btor_exec = self.project_root_dir + "/bin_solvers/bin/boolector"
        self.bitwuzla_exec = self.project_root_dir + "/bin_solvers/bin/bitwuzla"
        self.yices_exec = self.project_root_dir + "/bin_solvers/bin/yices-smt2"
        self.math_exec = self.project_root_dir + "/bin_solvers/bin/mathsat"
        self.caqe_exec = self.project_root_dir + "/bin_solvers/bin/caqe"
        self.q3b_exec = self.project_root_dir + "/bin_solvers/bin/q3b"

        # These values can be modified by CLI tools
        self.bin_solver_timeout = 30
        self.verifier_args = None  # the configuration of the prover.py
        self.efsmt_args = None  # the configuration of the efsmt_solver.py   # Not used for now

    def check_available(self, solver_name: str) -> bool:
        """Check if a solver executable exists.
        
        Args:
            solver_name: Name of the solver to check
            
        Returns:
            bool: True if the solver executable exists, False otherwise
        """
        solver_map = {
            "z3": self.z3_exec,
            "cvc5": self.cvc5_exec,
            "btor": self.btor_exec,
            "bitwuzla": self.bitwuzla_exec,
            "yices": self.yices_exec,
            "mathsat": self.math_exec,
            "caqe": self.caqe_exec,
            "q3b": self.q3b_exec
        }
        return Path(solver_map.get(solver_name, "")).exists()


# Create a default instance
config = EFMCConfig()

# For backward compatibility and to allow CLI tools to modify these values
project_root_dir = config.project_root_dir
z3_exec = config.z3_exec
cvc5_exec = config.cvc5_exec
btor_exec = config.btor_exec
bitwuzla_exec = config.bitwuzla_exec
yices_exec = config.yices_exec
math_exec = config.math_exec
caqe_exec = config.caqe_exec
q3b_exec = config.q3b_exec

# These variables can be modified by CLI tools
# When they're modified, we'll update the singleton instance too
g_bin_solver_timeout = config.bin_solver_timeout
g_verifier_args = config.verifier_args
g_efsmt_args = config.efsmt_args


# Add functions to update the config when CLI tools modify the globals
def update_config_from_globals():
    """Update the singleton config from global variables
    When a CLI tool modifies one of the global variables, you can call update_config_from_globals() to ensure the singleton is updated.
    """
    config.bin_solver_timeout = g_bin_solver_timeout
    config.verifier_args = g_verifier_args
    config.efsmt_args = g_efsmt_args


def update_globals_from_config():
    """Update global variables from the singleton config
    If you modify the singleton directly, you can call update_globals_from_config() to update the globals.
    """
    global g_bin_solver_timeout, g_verifier_args, g_efsmt_args
    g_bin_solver_timeout = config.bin_solver_timeout
    g_verifier_args = config.verifier_args
    g_efsmt_args = config.efsmt_args


if __name__ == "__main__":
    print(config.project_root_dir)
    print(config.z3_exec)
    print(config.cvc5_exec)
    print(config.btor_exec)
    print(config.bitwuzla_exec)
    print(config.yices_exec)
    print(config.math_exec)
    print(config.caqe_exec)
    print(config.q3b_exec)
