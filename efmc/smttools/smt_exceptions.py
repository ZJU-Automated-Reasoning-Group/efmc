class SMTError(Exception):
    """
    Top level Exception object for custom exception hierarchy
    """
    pass


class SmtlibError(SMTError):
    pass


class SolverError(SmtlibError):
    pass
