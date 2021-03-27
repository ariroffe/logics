from input_validator import validate_input
from Q_functions import choose

# ----------------------------------------------------------------------------------------------------------------------
# First two f functions


def Q_US(n, p, C, validate=True, Q_US_prev_values=None):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: integer, representing the number of formulae with at most profundity n and containing (all or some) P
    """
    if validate:
        validate_input(n, p, C)
    if n < 0:
        return [0, Q_US_prev_values]
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()
    if n == 0:
        Q_US_prev_values[(n, p)] = p
        return [p, Q_US_prev_values]
    else:
        if (n, p) in Q_US_prev_values:
            return [Q_US_prev_values[(n, p)], Q_US_prev_values]
        Cmax = max(C) if C else 0
        new_value = p + sum(len(C[i]) * (Q_US(n-1, p, C, False, Q_US_prev_values)[0] ** i) for i in range(1, Cmax+1) if i in C)
        Q_US_prev_values[(n, p)] = new_value
        return [new_value, Q_US_prev_values]


def Q_ES(n, p, C, validate=True, Q_US_prev_values=None, Q_ES_prev_values=None):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: integer, representing the number of formulae with exactly profundity n and containing (all or some) P
    """
    if validate:
        validate_input(n, p, C)
    if Q_ES_prev_values is None:
        Q_ES_prev_values = dict()
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()
    if n == 0:
        Q_ES_prev_values[(n, p)] = p
        return [p, Q_US_prev_values, Q_ES_prev_values]
    else:
        if (n, p) in Q_ES_prev_values:
            return [Q_ES_prev_values[(n, p)], Q_US_prev_values, Q_ES_prev_values]
        first = Q_US(n, p, C, False, Q_US_prev_values)
        second = Q_US(n-1, p, C, False, first[1])
        Q_US_prev_values.update(second[1])
        new_value = first[0] - second[0]
        Q_ES_prev_values[(n, p)] = new_value
        return [new_value, Q_US_prev_values, Q_ES_prev_values]


def Q_EA(n, p, C, validate=True, Q_US_prev_values=None, Q_ES_prev_values=None, Q_EA_prev_values=None):
    """
    :param n: zero or positive integer, depth
    :param p: positive integer, number of atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_EA_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: integer, representing the number of formulae with exactly profundity n and containing all P
        FINAL VERSION
    """
    if validate:
        validate_input(n, p, C)
    if Q_EA_prev_values is None:
        Q_EA_prev_values = dict()
    if Q_ES_prev_values is None:
        Q_ES_prev_values = dict()
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()
    if (n, p) in Q_EA_prev_values:
        return [Q_EA_prev_values[(n, p)], Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values]
    if p > max(C) ** n:
        Q_EA_prev_values[(n, p)] = 0
        return [0, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values]
    if n == 0 and p == 1:
        Q_EA_prev_values[(n, p)] = 1
        return [1, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values]
    else:
        initial_value = Q_ES(n, p, C, False, Q_US_prev_values, Q_ES_prev_values)
        result = initial_value[0]
        Q_US_prev_values.update(initial_value[1])
        Q_ES_prev_values.update(initial_value[2])
        for j in range(1, p):
            new_term = Q_EA(n, j, C, False, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values)
            result -= choose(p, j) * new_term[0]
            Q_US_prev_values.update(new_term[1])
            Q_ES_prev_values.update(new_term[2])
        Q_EA_prev_values[(n, p)] = result
        return [result, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values]
