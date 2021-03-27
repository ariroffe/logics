import random
from itertools import product
from bisect import bisect_right

from Q_functions import Q_US, Q_ES, Q_EA
from input_validator import validate_input2


# ----------------------------------------------------------------------------------------------------------------------
# G_ES_biased


def G_ES_biased(n, P, C, validate=True):
    """
    Biased version of G_ES
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with exactly n depth and containing (all or some) P
    """
    if validate:
        validate_input2(n, P, C)

    if n == 0:
        return random.choice(tuple(P))

    else:
        all_constants = set()
        for c in C:
            all_constants = all_constants | C[c]

        constant = random.choice(tuple(all_constants))
        arity = [a for a in C if constant in C[a]][0]
        s_arguments = dict()

        i = random.randint(1, arity)
        s_arguments[i] = G_ES_biased(n-1, P, C, False)

        for x in set(range(1, arity+1)) - {i}:
            j = random.randint(0, n-1)
            s_arguments[x] = G_ES_biased(j, P, C, False)

        s = constant + '('
        for y in sorted(s_arguments):
            s += s_arguments[y] + ', '
        s = s[:-2] + ')'

        return s


# ----------------------------------------------------------------------------------------------------------------------
# G_US_biased


def G_US_biased(n, P, C, validate=True):
    """
    Biased version of G_US
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with up to n depth and containing (all or some) P
    """
    if validate:
        validate_input2(n, P, C)

    # Choice of depth
    chosen_depth = random.randint(0, n)
    return G_ES_biased(chosen_depth, P, C, False)


# ----------------------------------------------------------------------------------------------------------------------
# G_EA_biased


def G_EA_biased(n, P, C, validate=True):
    """
    Biased version of G_EA. Uses a brute force approach, very inefficient.
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with exactly n depth and containing all P
    """

    if validate:
        validate_input2(n, P, C)

    while True:
        acceptable = True
        f = G_ES_biased(n, P, C)
        for at in P:
            if at not in f:
                acceptable = False
        if acceptable:
            return f


# ----------------------------------------------------------------------------------------------------------------------
# G_ES_uniform


def G_ES_uniform(n, P, C, validate=True):
    """
    Uniform version of G_ES
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with exactly n depth and containing (all or some) P
    """
    if validate:
        validate_input2(n, P, C)

    if n == 0:
        return random.choice(tuple(P))

    else:
        all_constants = list()
        for c in C:
            all_constants.extend(list(C[c]))

        # Weighted choice of the logical constant
        constant_weights = get_constant_weights(n, P, C, all_constants)
        denominator = Q_ES(n, len(P), C, validate=False)
        assert denominator == constant_weights[-1]
        try:
            rnd = random.random() * denominator
        except OverflowError:
            # If the denominator is too large, Python cannot compute the float. The follwing will be almost uniform
            rnd = random.randint(0, denominator - 1)
        chosen_index = bisect_right(constant_weights, rnd)
        constant = all_constants[chosen_index]

        arity = [a for a in C if constant in C[a]][0]
        s_arguments = dict()

        # Weighted generation of a distribution of depths
        possible_depth_distributions = [x for x in product(range(0, n), repeat=arity) if n - 1 in x]
        depth_weights = get_depth_weights(possible_depth_distributions, P, C)
        denominator2 = depth_weights[-1]
        try:
            rnd2 = random.random() * denominator2
        except OverflowError:
            rnd2 = random.randint(0, denominator2 - 1)
        chosen_index2 = bisect_right(depth_weights, rnd2)
        chosen_depths = possible_depth_distributions[chosen_index2]

        for x in range(0, len(chosen_depths)):
            s_arguments[x] = G_ES_uniform(chosen_depths[x], P, C, False)

        s = constant + '('
        for y in sorted(s_arguments):
            s += s_arguments[y] + ', '
        s = s[:-2] + ')'

        return s


def get_constant_weights(n, P, C, all_constants):
    """
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param all_constants: list of strings, all logical constants of all arities
    :return: list of integers, representing the accumulated numerators of the weighing function
    """
    weights = []
    totals = 0

    for constant in all_constants:
        constant_arity = [x for x in C if constant in C[x]][0]
        num = Q_US(n-1, len(P), C, validate=False) ** constant_arity - \
              Q_US(n-2, len(P), C, validate=False) ** constant_arity
        totals += num
        weights.append(totals)

    return weights


def get_depth_weights(possible_weight_distributions, P, C):
    """
    :param possible_weight_distributions: list of tuples of integers (representing depths of arguments)
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :return: list of integers, representing the accumulated numerators of the weighing function
    """
    weights = []
    totals = 0

    for distribution in possible_weight_distributions:
        distrib_total = 1
        for argument in distribution:
            distrib_total = distrib_total * Q_ES(argument, len(P), C, validate=False)
        totals += distrib_total
        weights.append(totals)

    return weights


# ----------------------------------------------------------------------------------------------------------------------
# G_US_uniform


def G_US_uniform(n, P, C, validate=True):
    """
    Uniform version of G_US
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with up to n depth and containing (all or some) P
    """

    if validate:
        validate_input2(n, P, C)

    # Weighted choice of depth
    possible_depths = list(range(0, n+1))
    depth_weights = get_depth_weights2(possible_depths, P, C)
    denominator = Q_US(n, len(P), C, validate=False)
    try:
        rnd = random.random() * denominator
    except OverflowError:
        rnd = random.randint(0, denominator - 1)
    chosen_index = bisect_right(depth_weights, rnd)
    chosen_depth = possible_depths[chosen_index]

    return G_ES_uniform(chosen_depth, P, C, False)


def get_depth_weights2(possible_depths, P, C):
    """
    :param possible_depths: list of integers
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :return: list of integers, representing the accumulated numerators of the weighing function
    """
    weights = []
    totals = 0

    for depth in possible_depths:
        num = Q_ES(depth, len(P), C, validate=False)
        totals += num
        weights.append(totals)

    return weights


# ----------------------------------------------------------------------------------------------------------------------
# G_EA_uniform


def G_EA_uniform(n, P, C, validate=True):
    """
    Uniform version of G_EA
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: random formula with exactly n depth and containing all P
    """
    if validate:
        validate_input2(n, P, C)
    max_C = max(C)
    if len(P) > max_C ** n:
        raise ValueError("len(P) can be at most n ** max(C)")

    if n == 0 and len(P) == 1:
        return tuple(P)[0]
    possible_distribs = list()
    for arity in C:
        possible_distribs.extend(G_EA_possible_distributions(arity, n-1, P, max_C))
    weights = get_G_EA_weights(possible_distribs, C)
    denominator = Q_EA(n, len(P), C, validate=False)
    assert denominator == weights[-1]
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
        formula_arguments.append(G_EA_uniform(chosen_distrib[0][index], chosen_distrib[1][index], C, False))

    formula_arguments = ', '.join(formula_arguments)
    formula = f'{chosen_constant}({formula_arguments})'
    return formula


def powerset(base_set):
    """
    :param base_set: set
    :return: list of lists, powerset of the original set
    """
    pset = [[]]
    for elem in base_set:
        pset.extend([x + [elem] for x in pset])
    return pset


def union_set(base_set):
    """
    :param base_set: set of sets
    :return: set, union set of base_set
    """
    uset = set()
    for x in base_set:
        uset = uset | x
    return uset


def G_EA_possible_distributions(arity, n, P, max_C):
    """
    :param arity: positive integer
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param max_C: integer, maximum arity of the constants of the language
    :return: list, elements are of the form ((0, 1), ({'q'}, {'q', 'p'})) (1st elem contains depths, 2nd subsets of P)
    """
    pset = powerset(P)
    pset.remove([])
    pset = [set(x) for x in pset]

    P_distribs = tuple(product(pset, repeat=arity))
    possible_distribs = list()
    for ndist in product(range(0, n+1), repeat=arity):
        if n in ndist:
            for pdist in P_distribs:
                if set(union_set(pdist)) == P:
                    admissible = True
                    for x in range(len(ndist)):
                        if len(pdist[x]) > max_C ** ndist[x]:
                            admissible = False
                    if admissible:
                        possible_distribs.append((ndist, pdist))
    return possible_distribs


def get_G_EA_weights(possible_distribs, C):
    """
    :param possible_distribs: list of the form returned in the function above
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :return: list of integers, representing the accumulated numerators of the weighing function
    """
    weights = []
    totals = 0

    for distrib in possible_distribs:
        num = 1
        for index in range(len(distrib[0])):
            num *= Q_EA(distrib[0][index], len(distrib[1][index]), C, validate=False)
        num *= len(C[len(distrib[0])])  # Multiply by the number of connectives of that arity
        totals += num
        weights.append(totals)

    return weights
