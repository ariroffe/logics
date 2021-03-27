from math import factorial

from input_validator import validate_input


def Q_US(n, p, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: integer, representing the number of formulae with at most profundity n and containing (all or some) P
    """
    if validate:
        validate_input(n, p, C)
    if n < 0:
        return 0
    if n == 0:
        return p
    else:
        Cmax = max(C) if C else 0
        return p + sum(len(C[i]) * (Q_US(n-1, p, C, False) ** i) for i in range(1, Cmax+1) if i in C)


def Q_ES(n, p, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: integer, representing the number of formulae with exactly profundity n and containing (all or some) P
    """
    if validate:
        validate_input(n, p, C)
    if n == 0:
        return p
    else:
        return Q_US(n, p, C, False) - Q_US(n-1, p, C, False)


def choose(n, r):
    """
    :param n: zero or positive integer
    :param p: zero or positive integer
    :return: standard combinatorics combinations (nCr)
    """
    return factorial(n) // (factorial(n-r) * factorial(r))


def Q_EA(n, p, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: integer, representing the number of formulae with exactly profundity n and containing all P
    """
    if validate:
        validate_input(n, p, C)
    if p > max(C) ** n:
        return 0
    else:
        return Q_ES(n, p, C, False) - sum(choose(p, j) * Q_EA(n, j, C, False) for j in range(1, p))
