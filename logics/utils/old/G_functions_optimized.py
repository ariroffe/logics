import random
from itertools import product
from bisect import bisect_right

from Q_functions_optimized import Q_US, Q_ES, Q_EA
from G_functions import powerset, union_set, G_EA_possible_distributions
from input_validator import validate_input2


# ----------------------------------------------------------------------------------------------------------------------
# G_ES_uniform


def G_ES_uniform(iterations, n, P, C, validate=True, Q_US_prev_values=None, Q_ES_prev_values=None):
    """
    Wrapper for the optimized uniform version of G_ES
    :param iterations: positive integer, number of formulae to generate
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: list of random formulae with exactly n depth and containing (all or some) P
    """

    if Q_ES_prev_values is None:
        Q_ES_prev_values = dict()
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()

    if validate:
        validate_input2(n, P, C)

    formulae = list()
    for i in range(iterations):
        f = G_ES_uniform2(n, P, C, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(f[1])
        Q_ES_prev_values.update(f[2])
        f = f[0]
        formulae.append(f)

    return formulae


def G_ES_uniform2(n, P, C, Q_US_prev_values, Q_ES_prev_values):
    """
    Optimized uniform version of G_ES
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param Q_US_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (random formula with exactly n depth and containing (all or some) P, prev_Q_US, prev_Q_ES)
    """
    if n == 0:
        return random.choice(tuple(P)), Q_US_prev_values, Q_ES_prev_values

    else:
        all_constants = list()
        for c in C:
            all_constants.extend(list(C[c]))

        # Weighted choice of the logical constant
        constant_weights = get_constant_weights(n, P, C, all_constants, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(constant_weights[1])
        Q_ES_prev_values.update(constant_weights[2])
        constant_weights = constant_weights[0]
        denominator = constant_weights[-1]
        try:
            rnd = random.random() * denominator
        except OverflowError:
            # If the denominator is too large, Python cannot compute the float. The follwing will be almost uniform
            rnd = random.randint(0, denominator-1)
        chosen_index = bisect_right(constant_weights, rnd)
        constant = all_constants[chosen_index]

        arity = [a for a in C if constant in C[a]][0]
        s_arguments = dict()

        # Weighted generation of a distribution of depths
        possible_depth_distributions = [x for x in product(range(0, n), repeat=arity) if n-1 in x]
        depth_weights = get_depth_weights(possible_depth_distributions, P, C, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(depth_weights[1])
        Q_ES_prev_values.update(depth_weights[2])
        depth_weights = depth_weights[0]
        denominator2 = depth_weights[-1]
        try:
            rnd2 = random.random() * denominator2
        except OverflowError:
            rnd2 = random.randint(0, denominator2-1)
        chosen_index2 = bisect_right(depth_weights, rnd2)
        chosen_depths = possible_depth_distributions[chosen_index2]

        for x in range(0, len(chosen_depths)):
            prev = G_ES_uniform2(chosen_depths[x], P, C, Q_US_prev_values, Q_ES_prev_values)
            Q_US_prev_values.update(prev[1])
            Q_ES_prev_values.update(prev[2])
            s_arguments[x] = prev[0]

        s = constant + '('
        for y in sorted(s_arguments):
            s += s_arguments[y] + ', '
        s = s[:-2] + ')'

        return s, Q_US_prev_values, Q_ES_prev_values


def get_constant_weights(n, P, C, all_constants, Q_US_prev_values, Q_ES_prev_values):
    """
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param all_constants: list of strings, all logical constants of all arities
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (list of integers, representing the accumulated numerators of the weighing function, prev_values)
    """
    weights = []
    totals = 0

    for constant in all_constants:
        constant_arity = [x for x in C if constant in C[x]][0]

        num1 = Q_US(n-1, len(P), C, False, Q_US_prev_values)
        Q_US_prev_values.update(num1[1])
        num2 = Q_US(n-2, len(P), C, False, Q_US_prev_values)
        Q_US_prev_values.update(num2[1])

        num = num1[0] ** constant_arity - num2[0] ** constant_arity
        totals += num
        weights.append(totals)

    return weights, Q_US_prev_values, Q_ES_prev_values


def get_depth_weights(possible_weight_distributions, P, C, Q_US_prev_values, Q_ES_prev_values):
    """
    :param possible_weight_distributions: list of tuples of integers (representing depths of arguments)
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (list of integers, representing the accumulated numerators of the weighing function, prev_values)
    """
    weights = []
    totals = 0

    for distribution in possible_weight_distributions:
        distrib_total = 1
        for argument in distribution:
            num = Q_ES(argument, len(P), C, False, Q_US_prev_values, Q_ES_prev_values)
            Q_US_prev_values.update(num[1])
            Q_ES_prev_values.update(num[2])
            num = num[0]
            distrib_total *= num
        totals += distrib_total
        weights.append(totals)

    return weights, Q_US_prev_values, Q_ES_prev_values


# ----------------------------------------------------------------------------------------------------------------------
# G_US_uniform


def G_US_uniform(iterations, n, P, C, validate=True, Q_US_prev_values=None, Q_ES_prev_values=None):
    """
    Optimized uniform version of G_US
    :param iterations: positive integer, number of formulae to generate
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: list of random formulae with up to n depth and containing (all or some) P
    """

    if Q_ES_prev_values is None:
        Q_ES_prev_values = dict()
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()

    if validate:
        validate_input2(n, P, C)

    formulae = list()
    for i in range(iterations):
        # Weighted choice of depth
        possible_depths = list(range(0, n+1))
        depth_weights = get_depth_weights2(possible_depths, P, C, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(depth_weights[1])
        Q_ES_prev_values.update(depth_weights[2])
        depth_weights = depth_weights[0]
        denominator = depth_weights[-1]

        try:
            rnd = random.random() * denominator
        except OverflowError:
            rnd = random.randint(0, denominator-1)
        chosen_index = bisect_right(depth_weights, rnd)
        chosen_depth = possible_depths[chosen_index]

        f = G_ES_uniform2(chosen_depth, P, C, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(f[1])
        Q_ES_prev_values.update(f[2])
        f = f[0]
        formulae.append(f)

    return formulae


def get_depth_weights2(possible_depths, P, C, Q_US_prev_values, Q_ES_prev_values):
    """
    :param possible_depths: list of integers
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param Q_US_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (list of integers, representing the accumulated numerators of the weighing function, prev_values)
    """
    weights = []
    totals = 0

    for depth in possible_depths:
        num = Q_ES(depth, len(P), C, False, Q_US_prev_values, Q_ES_prev_values)
        Q_US_prev_values.update(num[1])
        Q_ES_prev_values.update(num[2])
        totals += num[0]
        weights.append(totals)

    return weights, Q_US_prev_values, Q_ES_prev_values


# ----------------------------------------------------------------------------------------------------------------------
# G_EA_uniform


def G_EA_uniform(iterations, n, P, C, validate=True, Q_US_prev_values=None, Q_ES_prev_values=None, Q_EA_prev_values=None):
    """
    Wrapper for the optimized uniform version of G_ES
    :param iterations: positive integer, number of formulae to generate
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :param Q_US_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :param Q_EA_prev_values: None or dict, saves the result of previous values so that it does not repeat calculations
    :return: list of random formulae with exactly n depth and containing all P
    """

    if Q_EA_prev_values is None:
        Q_EA_prev_values = dict()
    if Q_ES_prev_values is None:
        Q_ES_prev_values = dict()
    if Q_US_prev_values is None:
        Q_US_prev_values = dict()

    if validate:
        validate_input2(n, P, C)

    if len(P) > max(C) ** n:
        raise ValueError("len(P) can be at most n ** max(C)")

    formulae = list()
    for i in range(iterations):
        f = G_EA_uniform2(n, P, C, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values)
        Q_US_prev_values.update(f[1])
        Q_ES_prev_values.update(f[2])
        Q_EA_prev_values.update(f[3])
        f = f[0]
        formulae.append(f)

    return formulae


def G_EA_uniform2(n, P, C, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values):
    """
    Optimized uniform version of G_EA
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param Q_US_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_EA_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (random formula with exactly n depth and containing (all or some) P, prev_Q_US, prev_Q_ES, prev_Q_EA)
    """
    if n == 0:
        return tuple(P)[0], Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values

    else:
        all_constants = list()
        for c in C:
            all_constants.extend(list(C[c]))

        possible_distribs = list()
        for arity in C:
            possible_distribs.extend(G_EA_possible_distributions(arity, n - 1, P, max(C)))

        weights = get_G_EA_weights(possible_distribs, C,
                                   Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values)
        Q_US_prev_values.update(weights[1])
        Q_ES_prev_values.update(weights[2])
        Q_EA_prev_values.update(weights[3])
        weights = weights[0]
        denominator = weights[-1]

        try:
            rnd = random.random() * denominator
        except OverflowError:
            rnd = random.randint(0, denominator - 1)
        chosen_index = bisect_right(weights, rnd)
        chosen_distrib = possible_distribs[chosen_index]
        chosen_arity = len(chosen_distrib[0])
        chosen_constant = random.choice(tuple(C[chosen_arity]))

        formula_arguments = list()
        for index in range(len(chosen_distrib[0])):
            f = G_EA_uniform2(chosen_distrib[0][index], chosen_distrib[1][index], C,
                              Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values)
            Q_US_prev_values.update(f[1])
            Q_ES_prev_values.update(f[2])
            Q_EA_prev_values.update(f[3])
            f = f[0]
            formula_arguments.append(f)

        formula_arguments = ', '.join(formula_arguments)
        formula = f'{chosen_constant}({formula_arguments})'
        return formula, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values


def get_G_EA_weights(possible_distribs, C, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values):
    """
    :param possible_distribs: list of the form returned in the function above
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param Q_US_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_ES_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :param Q_EA_prev_values: dict, saves the result of previous values so that it does not repeat calculations
    :return: tuple (list of integers, representing the accumulated numerators of the weighing function, prev_values)
    """
    weights = []
    totals = 0

    for distrib in possible_distribs:
        num = 1
        for index in range(len(distrib[0])):
            val = Q_EA(distrib[0][index], len(distrib[1][index]), C, False,
                        Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values)
            Q_US_prev_values.update(val[1])
            Q_ES_prev_values.update(val[2])
            Q_EA_prev_values.update(val[3])
            num *= val[0]
        num *= len(C[len(distrib[0])])  # Multiply by the number of connectives of that arity
        totals += num
        weights.append(totals)

    return weights, Q_US_prev_values, Q_ES_prev_values, Q_EA_prev_values
