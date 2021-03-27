from random import choice, sample, randint
from itertools import product

try:
    from utils_formula_parser import atomics, FOL_variables, FOL_predicates, FOL_individual_constants
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import atomics, FOL_variables, FOL_predicates, FOL_individual_constants

# ----------------------------------------------------------------------------------------------------------------------
# PROPOSITIONAL FORMULAS


def random_propositional_formula(max_depth, max_atomics, logic):
    """Makes a choice of depth and atomics and calls random_prop_formula2"""
    depth = randint(0, max_depth)
    if depth == 0:
        atomics_to_be_used = atomics[:1]
    else:
        atomics_to_be_used = atomics[:randint(1, max_atomics)]
        if len(atomics_to_be_used) > depth + 1:
            atomics_to_be_used = atomics_to_be_used[:depth + 2]
    formula = random_propositional_formula2(depth, atomics_to_be_used, logic)
    return formula


def random_propositional_formula2(depth, atomics_to_be_used, logic):
    """Generates a random propositional formula
    Returns [the formula, profundity, used letters]"""

    formula_structure = random_propositional_structure(len(atomics_to_be_used), depth, logic)
    formula = replace_propositional_letters(formula_structure, atomics_to_be_used)

    return formula


def random_propositional_structure(num_atomics, depth, logic):
    """Places where a letter must go are marked with $
       num_atomics is the MINIMUM number of $s that are needed"""

    if depth == 0:
        return '$'

    constants2 = logic.constants()[:]
    if depth + 1 == num_atomics:
        # Choose only from the binary operations
        constants2 = logic.constants(2)[:]
    # If there is depth left, choose an operation
    chosen_operation = choice(constants2)

    # Unary operation
    if chosen_operation in logic.constants(1):
        formula_inside = random_propositional_structure(num_atomics, depth - 1, logic)
        # formula = chosen_operation + formula_inside
        formula = f'{chosen_operation}{formula_inside}'
        return formula

    else:
        # We have to make sure that at least one of the sides has the required depth
        # Just build two operations (one of them with complete depth, the other one random)
        # And then make a choice as to where to put the complete one

        formula1 = random_propositional_structure(1, depth - 1, logic)
        formula1_num_letters = formula1.count('$')

        formula2_num_letters = max(1, num_atomics - formula1_num_letters)
        formula2 = random_propositional_structure(formula2_num_letters,
                                                  randint(formula2_num_letters - 1, depth - 1), logic)

        if choice([True, False]):
            # formula = "(" + formula1 + " " + chosen_operation + " " + formula2 + ")"
            formula = f'({formula1} {chosen_operation} {formula2})'
        else:
            # formula = "(" + formula2 + " " + chosen_operation + " " + formula1 + ")"
            formula = f'({formula2} {chosen_operation} {formula1})'

        return formula


def replace_propositional_letters(formula_structure, atomic_replacements):

    replacement_indexes = [x for x in range(len(formula_structure)) if formula_structure[x] == '$']

    # Each atomic chooses one position
    for a in atomic_replacements:
        chosen_position = choice(replacement_indexes)
        before = formula_structure[:chosen_position]
        after = formula_structure[chosen_position + 1:]
        formula_structure = f'{before}{a}{after}'
        # formula_structure = formula_structure[:chosen_position] + a + formula_structure[chosen_position + 1:]
        replacement_indexes.remove(chosen_position)

    # If there are still $s left, assign random atomics to them
    while '$' in formula_structure:
        first_apperance = formula_structure.index('$')
        before = formula_structure[:first_apperance]
        after = formula_structure[first_apperance + 1:]
        formula_structure = f'{before}{choice(atomic_replacements)}{after}'
        # formula_structure = formula_structure[:first_apperance] + choice(atomic_replacements) + \
        #                     formula_structure[first_apperance + 1:]

    return formula_structure


def random_propositional_argument(number_premises, max_profund, max_letters, logic):
    premises = list()
    for num in range(number_premises):
        premises.append(random_propositional_formula(max_profund, max_letters, logic))
    conclusion = random_propositional_formula(max_profund, max_letters, logic)
    return [*premises, conclusion]


# ----------------------------------------------------------------------------------------------------------------------
# SETS


def random_set(max_cardinality):
    """Returns the set AND A LIST! (so that its members are ordered for display)"""
    cardinality = randint(0, max_cardinality)
    set_to_sample = set(range(1, max_cardinality + 1))
    chosen_list = sample(set_to_sample, cardinality)
    chosen_list.sort()
    chosen_list = [str(x) for x in chosen_list]
    chosen_set = frozenset(chosen_list)
    return [chosen_set, chosen_list]


def random_set_operation(sets, operations_to_use, depth):

    formula_structure = random_set_operation_structure(len(sets), operations_to_use, depth)
    formula = replace_set_letters(formula_structure, sets)
    return formula


def random_set_operation_structure(num_sets, operations_to_use, depth):
    """Places where a letter must go are marked with $
    num_sets is the MINIMUM number of $s that are needed
    Operations_to_use is a list (for ex ['union', 'inters', 'cartp'])"""

    if depth == 0:
        return '$'

    operations2 = operations_to_use[:]
    if depth + 1 == num_sets:
        # Choose only from the binary operations
        if '℘' in operations2:
            operations2.remove('℘')
    # If there is depth left, choose an operation
    chosen_operation = choice(operations2)

    # The only unary operation
    if chosen_operation == '℘':
        formula_inside = random_set_operation_structure(num_sets, operations_to_use, depth-1)
        if formula_inside[0] == '(' and formula_inside[-1] == ')':
            formula_inside = formula_inside[1:-1]
        formula = f'℘({formula_inside})'
        return formula

    else:
        # We have to make sure that at least one of the sides has the required depth
        # Just build two operations (one of them with complete depth, the other one random)
        # And then make a choice as to where to put the complete one

        formula1 = random_set_operation_structure(1, operations_to_use, depth - 1)
        formula1_num_sets = formula1.count('$')

        formula2_num_sets = max(1, num_sets - formula1_num_sets)
        formula2 = random_set_operation_structure(formula2_num_sets, operations_to_use,
                                                  randint(formula2_num_sets - 1, depth - 1))

        if choice([True, False]):
            formula = f'{chosen_operation}({formula1},{formula2})'
        else:
            formula = f'{chosen_operation}({formula2},{formula1})'

        return formula


def replace_set_letters(formula_structure, sets):
    """Gets a string with $ symbols inside, replaces them with the sets (each set appears at least once, then random)
    SETS (names) MUST BE ONE CHARACTER LONG"""

    replacement_indexes = [x for x in range(len(formula_structure)) if formula_structure[x] == '$']

    # Each set chooses one position
    for s in sets:
        chosen_position = choice(replacement_indexes)
        formula_structure = formula_structure[:chosen_position] + s + formula_structure[chosen_position+1:]
        replacement_indexes.remove(chosen_position)

    # If there are still $s left, assign random sets to them
    while '$' in formula_structure:
        first_apperance = formula_structure.index('$')
        formula_structure = formula_structure[:first_apperance] + choice(sets) + formula_structure[first_apperance+1:]

    return formula_structure


# ----------------------------------------------------------------------------------------------------------------------
# FIRST ORDER


def random_predicate_formula(num_variables, depth, max_arity, max_constants, logic):
    # Depth has to be at least the number of bound variables
    # Max arity has to be at least the number of bound variables

    formula_structure = random_predicate_structure(num_variables, depth, logic)
    formula_structure = replace_predicate_variables(formula_structure, num_variables)
    formula_structure = replace_predicate_atomics1(formula_structure, logic)
    formula_structure = replace_predicate_atomics2(formula_structure, max_arity)
    formula_structure = replace_predicate_atomics3(formula_structure, max_constants, logic)

    return formula_structure


def random_predicate_structure(num_variables, depth, logic):
    """Places where a letter must go are marked with $
       Places where a variable must go are marked with %"""

    if depth == 0:
        return '$'

    constants2 = logic.constants()[:]
    constants2.extend(logic.quantifiers[:])
    if depth == num_variables:
        # Choose only from the quantifiers
        constants2 = logic.quantifiers[:]
    elif num_variables == 0:
        # Don't choose from the quantifiers (otherwise it puts spurious quantifiers Vx Ex Phi)
        constants2 = logic.constants()[:]
    # If there is depth left, choose an operation
    chosen_operation = choice(constants2)

    # Unary operation
    if chosen_operation in logic.constants(1):
        formula_inside = random_predicate_structure(num_variables, depth - 1, logic)
        # formula = chosen_operation + formula_inside
        formula = f'{chosen_operation}{formula_inside}'
        return formula

    # Quantifier
    elif chosen_operation in logic.quantifiers:
        formula_inside = random_predicate_structure(num_variables - 1, depth - 1, logic)
        formula = f'{chosen_operation}% {formula_inside}'
        return formula

    # Binary
    else:
        # We have to make sure that at least one of the sides has the required depth
        # Just build two operations (one of them with complete depth, the other one random)
        # And then make a choice as to where to put the complete one

        formula1 = random_predicate_structure(randint(0, num_variables), depth - 1, logic)
        formula1_num_variables = formula1.count('%')

        formula2_num_variables = num_variables - formula1_num_variables
        formula2_depth = randint(formula2_num_variables, depth -1)
        formula2 = random_predicate_structure(formula2_num_variables, formula2_depth, logic)

        if choice([True, False]):
            formula = f'({formula1} {chosen_operation} {formula2})'
        else:
            formula = f'({formula2} {chosen_operation} {formula1})'

        return formula


def replace_predicate_variables(formula_structure, num_variables):

    variables = FOL_variables[:num_variables]
    replacement_indexes = [x for x in range(len(formula_structure)) if formula_structure[x] == '%']

    # Each variable chooses one position
    for a in variables:
        chosen_position = choice(replacement_indexes)
        before = formula_structure[:chosen_position]
        after = formula_structure[chosen_position + 1:]
        formula_structure = f'{before}{a}{after}'
        replacement_indexes.remove(chosen_position)

    # If there are still %s left, assign random variables to them
    while '%' in formula_structure:
        first_apperance = formula_structure.index('%')
        before = formula_structure[:first_apperance]
        after = formula_structure[first_apperance + 1:]
        formula_structure = f'{before}{choice(variables)}{after}'

    return formula_structure


def replace_predicate_atomics1(formula_structure, logic):
    """This function merely replaces the $s with the number of bound variables"""

    bound_variables = list()
    bound_variables_parentheses = list()

    for index in range(len(formula_structure)):

        if formula_structure[index] == '(':
            bound_variables_parentheses = [x + 1 for x in bound_variables_parentheses]

        elif formula_structure[index] == ')':
            bound_variables_parentheses = [x - 1 for x in bound_variables_parentheses]

        elif formula_structure[index] == '$':
            formula_structure = formula_structure[:index] + str(len(bound_variables)) + formula_structure[index+1:]

        if formula_structure[index] in logic.constants(2) and \
                bound_variables_parentheses and bound_variables_parentheses[-1] == 0:

            del bound_variables[-1]
            del bound_variables_parentheses[-1]

        if formula_structure[index] in FOL_variables:
            bound_variables.append(formula_structure[index])
            bound_variables_parentheses.append(0)

    return formula_structure


def replace_predicate_atomics2(form_structure, max_arity):
    """This one decides the arity of the predicates and then replaces the integers with letters followed with #"""

    formula_structure = form_structure
    formula_numbers = list(formula_structure)
    formula_numbers = [int(x) for x in formula_numbers if x.isdigit()]
    min_bounded = min(formula_numbers)
    max_bounded = max(formula_numbers)

    predicates = FOL_predicates[:randint(1, len(formula_numbers))]
    predicate_arity_dict = {p: None for p in predicates}

    pred_with_max = choice(predicates)
    predicate_arity_dict[pred_with_max] = randint(max_bounded, max_arity)

    for p in [x for x in predicates if x != pred_with_max]:
        predicate_arity_dict[p] = max(1, randint(min_bounded, max_arity))

    # Have each predicate choose a spot (if it can)
    for pred in predicates:
        replacement_indexes = [x for x in range(len(formula_structure)) if formula_structure[x].isdigit() and
                               int(formula_structure[x]) <= predicate_arity_dict[pred]]
        if replacement_indexes:
            chosen_index = choice(replacement_indexes)
            formula_structure = formula_structure[:chosen_index] + pred + "#" * predicate_arity_dict[pred] \
                                + formula_structure[chosen_index + 1:]

    # If there are still spaces left, put random predicates in them
    remaining_atomics = [x for x in formula_structure if x.isdigit()]
    while remaining_atomics:
        first_digit = remaining_atomics[0]
        first_digit_index = formula_structure.index(remaining_atomics[0])

        possible_predicates = [p for p in predicates if predicate_arity_dict[p] >= int(first_digit)]
        chosen_predicate = choice(possible_predicates)

        formula_structure = formula_structure[:first_digit_index] \
                            + chosen_predicate + "#" * predicate_arity_dict[chosen_predicate] \
                            + formula_structure[first_digit_index+1:]

        remaining_atomics = [x for x in formula_structure if x.isdigit()]

    return formula_structure


def replace_predicate_atomics3(formula_structure, max_constants, logic):
    """Replaces some #s with variables, the rest with constants"""

    for index1 in range(len(formula_structure)):

        if formula_structure[index1] in logic.quantifiers:
            variable = formula_structure[index1 + 1]
            variable_present = False
            # Get the reach of the quantifier
            reach = ''
            open_left = 0
            closing_right = 0
            other_variables = set()
            # The next character is a variable, and the next is a space: Vx Phi
            for index2 in range(index1 + 3, len(formula_structure)):
                if formula_structure[index2] == '(':
                    open_left += 1
                    reach += formula_structure[index2]
                elif formula_structure[index2] == ')':
                    closing_right += 1
                    if closing_right >= open_left:
                        break
                    reach += formula_structure[index2]
                elif formula_structure[index2] in logic.constants(2) and open_left == closing_right:
                    reach = reach[:-1]
                    break
                elif formula_structure[index2] in logic.quantifiers:
                    if formula_structure[index2+1] != variable:
                        other_variables.add(formula_structure[index2+1])
                    reach += formula_structure[index2]
                elif formula_structure[index2] == variable:
                    variable_present = True
                    reach += formula_structure[index2]
                else:
                    reach += formula_structure[index2]

            # If the variable is already present in the reach, do nothing
            if not variable_present:
                replacement_indexes = [x for x in range(index1, index1+len(reach)+3) if formula_structure[x] == '#']
                if len(replacement_indexes) - len(other_variables) != 0:
                    sample_size = randint(1, len(replacement_indexes) - len(other_variables))
                    replacements = sample(replacement_indexes, sample_size)
                    for index3 in replacements:
                        formula_structure = formula_structure[:index3] + variable + formula_structure[index3+1:]

    # If there are still #s left, replace them with constants
    if "#" in formula_structure:
        constants = FOL_individual_constants[:max_constants]
        while "#" in formula_structure:
            first_open = formula_structure.index("#")
            formula_structure = formula_structure[: first_open] + choice(constants) + formula_structure[first_open+1:]

    return formula_structure


def random_model(num_elements, formula, logic_name):
    # MAXIMUM NUM ELEMENTS IS 14

    dom = sample(list(range(1,15)), num_elements)
    dom.sort()

    model = dict()
    model['Domain'] = [str(x) for x in dom]

    ind_constants_copy = FOL_individual_constants[:num_elements]

    for elem in dom:
        chosen_constant = choice(ind_constants_copy)
        ind_constants_copy.remove(chosen_constant)
        model[chosen_constant] = str(elem)

    # Now infer the number and arity of predicates from the formula
    predicate_arity_dict = dict()
    predicates_in_formula = {p for p in formula if p in FOL_predicates}
    for p in predicates_in_formula:
        for index1 in range(len(formula)):
            if formula[index1] == p:
                arity = 0
                for index2 in range(index1+1, len(formula)):
                    if formula[index2] in FOL_individual_constants or formula[index2] in FOL_variables:
                        arity += 1
                    else:
                        break
                if formula[index1] not in predicate_arity_dict:
                    predicate_arity_dict[formula[index1]] = arity
                break

    # Give an extension and anti-extension to each predicate
    # Manually impose restrictions according to the chosen logic
    for predicate in predicate_arity_dict:
        if predicate_arity_dict[predicate] == 1:
            all_tuples = model["Domain"]
        elif predicate_arity_dict[predicate] > 1:
            all_tuples = list(product(model["Domain"], repeat=predicate_arity_dict[predicate]))

        model[predicate + "+"] = sorted(sample(all_tuples, randint(0, len(all_tuples))))

        if logic_name == "Classical":
            # Every possibiliy is either in the extension or the antiextension, and not both
            model[predicate + "-"] = sorted(list(set(all_tuples) - set(model[predicate + "+"])))
        elif logic_name == "LP" or logic_name == "RM3" or logic_name == "LFI1":
            # Every item that is not in the extension must be in the anti - but there might be some overlapping elements
            model[predicate + "-"] = list(set(all_tuples) - set(model[predicate + "+"]))
            model[predicate + "-"].extend(sample(model[predicate + "+"], randint(0, len(model[predicate + "+"]))))
            model[predicate + "-"].sort()
        elif logic_name == "K3" or logic_name == "Ł3":
            # No item overlaps, but there might be things that are not in the ext or antiext
            possible_anti = list(set(all_tuples) - set(model[predicate + "+"]))
            model[predicate + "-"] = sorted(sample(possible_anti, randint(0, len(possible_anti))))
        elif logic_name == "FDE":
            # Any value goes for the anti-extension
            model[predicate + "-"] = sorted(sample(all_tuples, randint(0, len(all_tuples))))

    return model
