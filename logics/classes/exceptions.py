class NotWellFormed(Exception):
    """
    Exception raised when a formula is not well-formed
    """
    pass


class IncorrectLevels(Exception):
    """
    Exception raised when an inference contains premises and/or conclusions of different levels
    """
    pass


class LevelsWarning(Warning):
    """
    Same as above but Warning instead of Exception
    """
    pass


class SolverError(Exception):
    """
    Exception raised when a solver fails to solve the given argument
    """
    pass


class SolverWarning(Warning):
    """
    Same as above but Warning instead of Exception
    """
    pass


class FormulaGeneratorError(Exception):
    """
    Exception raised when a formula generator cannot generate a formula / argument
    """
    pass


class DenotationError(Exception):
    """
    Exception raised when an error occurs in finding the denotation of a term in predicate logic
    """
    pass
