import matplotlib.pyplot as plt
import time
from copy import copy
from itertools import product

import Q_functions, Q_functions_optimized, G_functions
from input_validator import validate_input2


# ----------------------------------------------------------------------------------------------------------------------
# Q FUNCTIONS TESTS


def test_Qs(function, all_function, max_profundity, num_atomics, arity, verbose=False):
    """
        Tests the Q functions with the all_functions
        :param function: the numeric function to test
        :param all_function: the generator function of all formulae to test it with
        :param max_profundity: zero or positive integer, profundity up to which the test will take place
        :param num_atomics: positive integer, number of atomics up to which the test will take place
        :param arity: positive integer, maximum connective arity up to which the test will take place
        :param verbose: if True, will print the results of each test as it takes place. Else, prints only the global result
        :return:
    """
    max_profundity += 1
    num_atomics += 1
    arity += 1
    atomics = ["p"+str(x) for x in range(num_atomics)]
    for profundity in range(1, max_profundity):
        if verbose:
            print(f'\nProfundity {profundity}')
        for ats in range(1, num_atomics):
            for con in range(2, arity+1):
                constants_dict = {con-1: {str(con-1)}}

                generator = len(all_function(profundity, set(atomics[:ats]), constants_dict, False))
                calculation = function(profundity, set(atomics[:ats]), constants_dict, False)
                if generator != calculation:
                    return f"Error with n={profundity}, P={set(atomics[:ats])}, C={constants_dict}: {generator} vs {calculation}"
                if verbose:
                    print(f"\tn={profundity}, P={set(atomics[:ats])}, C={constants_dict}: {calculation} OK")

                constants_dict2 = {x: {str(x)} for x in range(1, con)}
                generator2 = len(all_function(profundity, set(atomics[:ats]), constants_dict2, False))
                calculation2 = function(profundity, set(atomics[:ats]), constants_dict2, False)
                if generator2 != calculation2:
                    return f"Error with n={profundity}, P={set(atomics[:ats])}, C={constants_dict2}: {generator2} vs {calculation2}"
                if verbose:
                    print(f"\tn={profundity}, P={set(atomics[:ats])}, C={constants_dict2}: {calculation2} OK")
    return "All tests passed"


# ----------------------------------------------------------------------------------------------------------------------
# G FUNCTIONS UNIFORMITY TESTS


def generate_distribution_Gs(iterations, G_function, all_function, n, P, C, optimized):
    """
    :param iterations: positive integer, number of formulae to be generated
    :param G_function: function that will generate the random formulae
    :param all_function: function that will generate all the formulae
    :param n: positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param optimized: if the G_function is in the optimized module, choose True, False otherwise
    :return: dict, keys: formulas, values: number of times generated
    """
    all_formulae = all_function(n, P, C, validate=False)
    times_generated = {f: 0 for f in all_formulae}

    if not optimized:
        for x in range(iterations):
            f = G_function(n, P, C, validate=False)
            times_generated[f] += 1
    else:
        f_list = G_function(iterations, n, P, C, validate=False)
        for f in f_list:
            times_generated[f] += 1

    return times_generated


def run_uniformity_test(iterations, G_function, all_G_function, n, P, C, draw=True, save=False, optimized=False):
    """
    :param iterations: positive integer, number of formulae to be generated
    :param G_function: function that will generate the random formulae
    :param all_function: function that will generate all the formulae
    :param n: positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integer (arities), values: sets of strings (constants of that arity)
    :param draw: If True, plots the distribution obtained. Otherwise prints the distribution to the console
    :param save: IF True, saves the plot to a file "Figure.png" in the wd
    :param optimized: if the G_function is in the optimized module, choose True, False otherwise
    :return: None. Only prints.
    """
    distrib = generate_distribution_Gs(iterations, G_function, all_G_function, n, P, C, optimized)
    if draw:
        #plt.figure(figsize=(4, 5))
        plt.bar(range(len(distrib)), list([x / sum(distrib.values()) for x in distrib.values()]), align='center')#, width=0.5)
        plt.xticks(range(len(distrib)), list(distrib.keys()), rotation='vertical')
        if save:
            plt.subplots_adjust(bottom=0.35)
            plt.savefig('Figure.png')
        plt.show()
    else:
        for x in distrib:
            print(x, distrib[x])


# ----------------------------------------------------------------------------------------------------------------------
# G FUNCTIONS BENCHMARK TEST

def benchmark(G_function, iterations, n, P, C, optimized):
    """
    :param G_function: function that will generate the random formulae
    :param iterations: positive integer, number of formulae to generate
    :param n: positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param optimized: if the G_function is in the optimized module, choose True, False otherwise
    :return: float, time elapsed from beggining to end
    """
    start = time.time()
    if not optimized:
        for x in range(iterations):
            G_function(n, P, C, validate=False)
    else:
        G_function(iterations, n, P, C, validate=False)
    return time.time() - start


# ----------------------------------------------------------------------------------------------------------------------
# ACTUALLY GENERATE ALL FORMULAE


def all_G_US(n, P, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: set of all formulae with at most n depth and containing (all or some) P
    """
    if validate:
        validate_input2(n, P, C)

    if n == 0:
        return P
    else:
        prev_formulae = all_G_US(n-1, P, C, False)
        all_formulae = copy(prev_formulae)
        for arity in C:
            possible_combinations = set(product(prev_formulae, repeat=arity))
            if arity in C:
                for logical_constant in C[arity]:
                    for combination in possible_combinations:
                        str_combination = str(combination).replace(',)', ')').replace("'", "").replace('"', '')
                        all_formulae.add(f'{logical_constant}{str_combination}')
        return all_formulae


def all_G_ES(n, P, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: set of all formulae with exactly n depth and containing (all or some) P
    """
    if type(P) == int:
        P = {f'p{x}' for x in range(P)}
    if validate:
        validate_input2(n, P, C)

    if n == 0:
        return P
    else:
        return all_G_US(n, P, C, False) - all_G_US(n-1, P, C, False)


def all_G_EA(n, P, C, validate=True):
    """
    :param n: zero or positive integer, depth
    :param P: set of strings, atomics
    :param C: dict, keys: positive integers (arities), values: sets of strings (constants of that arity)
    :param validate: if True, validates that the input provided is in the correct form
    :return: set of all formulae with exactly n depth and containing all P
    """
    if validate:
        validate_input2(n, P, C)

    if len(P) > max(C) ** n:
        return set()
    if n == 0 and len(P) == 1:
        return P
    else:
        discount = set()
        for p in P:
            P_copy = copy(P) - {p}
            discount = discount | (all_G_ES(n, P_copy, C, False))
        return all_G_ES(n, P, C, False) - discount


'''# For profiling purposes
if __name__ == '__main__':
    from G_functions_optimized import G_EA_uniform as G_EA_uniform_optimized
    from G_functions import G_EA_uniform
    import time

    start = time.time()
    for x in range(1000):
        G_EA_uniform(4, {'p', 'q', 'r', 's'}, {1: {'¬'}, 2: {'&'}}, validate=False)
    print(time.time() - start)
    
    start = time.time()
    G_EA_uniform_optimized(1000, 4, {'p', 'q', 'r', 's'}, {1: {'¬'}, 2:{'&'}}, validate=False)
    print(time.time() - start)'''
