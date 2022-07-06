class SMTError(Exception):
    """
    Top level Exception object for custom exception hierarchy
    """
    pass


class ExecutorError(SMTError):
    pass


class SmtlibError(SMTError):
    pass


class Z3NotFoundError(SmtlibError):
    pass


class SolverError(SmtlibError):
    pass


class SolverUnknown(SolverError):
    pass
