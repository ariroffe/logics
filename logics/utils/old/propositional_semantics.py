from itertools import product

from core.formula_parser import atomics, parse_propositional2, unparse_propositional_formula
from core.random_formula_generator import random_propositional_formula


# ----------------------------------------------------------------------------------------------------------------------
# OBTAIN VALUATIONS


def all_valuations(formula, logic, atomics_in_formula=None):
    """Returns a dictionary with the following structure:
    valuation[((p,1), (q,1))]=1
    valuation[((p,1), (q,0))}] = 0
    etc
    """
    if atomics_in_formula is None:
        atomics_in_formula = list()
    unparsed = str(formula)
    if not atomics_in_formula:
        atomics_in_formula = list({x for x in atomics if x in unparsed})
    combinations = list(product(logic.values, repeat=len(atomics_in_formula)))  # Combinations for atomics
    valuation = dict()
    for comb in combinations:
        key = tuple((atomics_in_formula[x], comb[x]) for x in range(len(comb)))
        valuation[key] = None
    for val_atomics in valuation:
        valuation[val_atomics] = individual_valuation(formula, val_atomics, logic)

    return valuation


def individual_valuation(formula, atomic_vals, logic):
    # Atomic
    if len(formula) == 1:
        for x in atomic_vals:
            if x[0] == formula[0]:
                if x[1] in logic.values:
                    return x[1]
                else:
                    raise ValueError(f'Value {x[1]} not in {str(logic)} logic')

    # Formula with unary connective
    if len(formula) == 2:
        return logic.t_function(formula[0], individual_valuation(formula[1], atomic_vals, logic))

    # Formula with binary connective
    if len(formula) == 3:
        return logic.t_function(formula[1], individual_valuation(formula[0], atomic_vals, logic),
                                individual_valuation(formula[2], atomic_vals, logic))


def individual_valuation_log(formula, atomic_vals, logic, counter=None):

    if counter is None:
        counter = 1

    # Atomic
    if len(formula) == 1:
        for x in atomic_vals:
            if x[0] == formula[0]:
                log = [[counter, formula, x[1], 'PREM', []]]
                return [x[1], log]

    # Formula with unary connective
    if len(formula) == 2:
        inside_result = individual_valuation_log(formula[1], atomic_vals, logic, counter)
        inside_val = inside_result[0]
        log = inside_result[1]
        last_step = log[-1][0]

        val = logic.t_function(formula[0], inside_val)
        log.append([last_step + 1, formula, val, formula[0], [last_step]])
        counter += 1
        return [val, log]

    # Formula with binary connective
    if len(formula) == 3 and formula[1] in logic.constants(2):
        form1_result = individual_valuation_log(formula[0], atomic_vals, logic, counter)
        form1_val = form1_result[0]
        log = form1_result[1]
        step1 = log[-1][0]

        # Optimization:
        # Disjunction with first value 1 is 1
        if formula[1] == '˅' and form1_val == '1':
            log.append([step1 + 1, formula, form1_val, formula[1], [step1]])
            return [form1_val, log]
        # Conditional with first value 0 is 1
        if formula[1] == '→' and form1_val == '0':
            log.append([step1 + 1, formula, '1', formula[1], [step1]])
            return ['1', log]
        # Conjunction with first value 0 is 0
        if formula[1] == '˄' and form1_val == '0':
            log.append([step1 + 1, formula, form1_val, formula[1], [step1]])
            return [form1_val, log]

        form2_result = individual_valuation_log(formula[2], atomic_vals, logic, step1 + 1)
        form2_val = form2_result[0]
        log.extend(form2_result[1])
        step2 = log[-1][0]
        val = logic.t_function(formula[1], form1_val, form2_val)

        # If the second formula is enough by itself, show only it in the log
        # Disjunction with second value 1 is 1
        if formula[1] == '˅' and form2_val == '1':
            log.append([step2 + 1, formula, val, formula[1], [step2]])
            return [val, log]
        # Conditional with second value 1 is 1
        if formula[1] == '→' and form2_val == '1':
            log.append([step2 + 1, formula, val, formula[1], [step2]])
            return [val, log]
        # Conjunction with first value 0 is 0
        if formula[1] == '˄' and form2_val == '0':
            log.append([step2 + 1, formula, val, formula[1], [step2]])
            return [val, log]
        # Else show both
        log.append([step2 + 1, formula, val, formula[1], [step1, step2]])
        return [val, log]


def get_subformulas(formula):
    """Returns a list of the subformulas of a formula"""
    subformulas = [formula]
    for subf in formula:
        if type(subf) == list:
            subformulas.extend(get_subformulas(subf))
    return subformulas

# ----------------------------------------------------------------------------------------------------------------------
# EVALUATE FORMULAS


def is_tautology(formula, logic):
    """Returns True if the formula gets conclusion designated in every valuation, False otherwise"""
    vs = all_valuations(formula, logic)
    for val in vs:
        if vs[val] not in logic.conclusion_designated_values:
            return False
    return True


def is_undesignated(formula, logic):
    """Returns True if the formula gets an undesignated value in every valuation, False otherwise"""
    vs = all_valuations(formula, logic)
    for val in vs:
        if vs[val] in logic.conclusion_designated_values:
            return False
    return True


def is_contingent(formula, logic):
    """Returns True if the formula has at least one designated an one undesignated valuation"""
    vs = all_valuations(formula, logic)
    desginated = False
    false = False
    for val in vs:
        if vs[val] not in logic.conclusion_designated_values:
            false = True
        if vs[val] in logic.conclusion_designated_values:
            desginated = True

    if desginated and false:
        return True
    return False


def is_logically_false(formula, logic):
    """Returns True if the formula is logically false in the logic (every valuation is in the false_values),
     False otherwise"""
    vs = all_valuations(formula, logic)
    for val in vs:
        if vs[val] not in logic.false_values:
            return False
    return True


# ----------------------------------------------------------------------------------------------------------------------
# GENERATE TAUTOLOGIES, UNDESIGNATED FORMULAS AND CONTINGENCIES


def generate_tautology(max_profund, max_letters, logic):
    rand_formula = random_propositional_formula(max_profund, max_letters, logic)
    formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
    count = 0
    while not is_tautology(formula, logic):
        if count == 100:
            raise ValueError("Could not find tautology")
        rand_formula = random_propositional_formula(max_profund, max_letters, logic)
        formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
        count += 1
    return formula


def generate_contradiction(max_profund, max_letters, logic):
    rand_formula = random_propositional_formula(max_profund, max_letters, logic)
    formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
    count = 0
    while not is_contingent(formula, logic):
        if count == 100:
            raise ValueError("Could not find contradiction")
        rand_formula = random_propositional_formula(max_profund, max_letters, logic)
        formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
        count += 1
    return formula


def generate_contingency(max_profund, max_letters, logic):
    rand_formula = random_propositional_formula(max_profund, max_letters, logic)
    formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
    count = 0
    while not is_contingent(formula, logic):
        if count == 1000:
            raise ValueError("Could not find contingency")
        rand_formula = random_propositional_formula(max_profund, max_letters, logic)
        formula = parse_propositional2(rand_formula.replace(" ", ""), logic)
        count += 1
    return formula


# ----------------------------------------------------------------------------------------------------------------------
# EVALUATE ARGUMENTS


def is_valid(logic, conclusion, *args, **kwargs):
    """Tells if an argument is valid in a logic, *args is a number of premises (formulas)"""

    # Gets the atomics present in the premises and conclusion
    total_atomics = {x for x in atomics if x in str(conclusion)}
    premises = list(args)
    premises.extend(list(kwargs.values()))
    for p in premises:
        total_atomics = total_atomics | {x for x in atomics if x in str(p)}
    total_atomics = list(total_atomics)

    # Gets valuations of the conclusion
    vals_conclusion = all_valuations(conclusion, logic, total_atomics)

    # Gets valuations of the premises
    dict_vals_premises = dict()
    count = 0
    for premise in premises:
        dict_vals_premises[count] = all_valuations(premise, logic, total_atomics)
        count += 1

    for val_atoms in vals_conclusion:  # This loops over the combinations of atomic valuations
        # If the conclusion is designated, moves on
        if vals_conclusion[val_atoms] not in logic.conclusion_designated_values:
            non_designated_prem = False
            for prem in dict_vals_premises:  # Loops over the premises
                # If any premise is not designated, exits the second loop,
                if dict_vals_premises[prem][val_atoms] not in logic.premise_designated_values:
                    non_designated_prem = True
                    break
            if not non_designated_prem:
                return False   # if all premises are designated and the conclusion is not designated, returns False

    return True


def preserves_falsity(logic, conclusion, *args, **kwargs):
    """Tells if an argument preserves falsity in a logic, *args is a number of premises (formulas)"""

    # Gets the atomics present in the premises and conclusion
    total_atomics = {x for x in atomics if x in str(conclusion)}
    premises = list(args)
    premises.extend(list(kwargs.values()))
    for p in premises:
        total_atomics = total_atomics | {x for x in atomics if x in str(p)}
    total_atomics = list(total_atomics)

    # Gets valuations of the conclusion
    vals_conclusion = all_valuations(conclusion, logic, total_atomics)

    # Gets valuations of the premises
    dict_vals_premises = dict()
    count = 0
    for premise in premises:
        dict_vals_premises[count] = all_valuations(premise, logic, total_atomics)
        count += 1

    for val_atoms in vals_conclusion:  # This loops over the combinations of atomic valuations
        # If the conclusion is not designated, moves on
        if vals_conclusion[val_atoms] in logic.conclusion_designated_values:
            designated_prem = False
            for prem in dict_vals_premises:  # Loops over the premises
                # If any premise is designated, exits the second loop,
                if dict_vals_premises[prem][val_atoms] in logic.premise_designated_values:
                    designated_prem = True
                    break
            if not designated_prem:
                return False  # if there are no designated premises and the conclusion is designated, returns False

    return True


def generate_valid_argument(number_premises, max_profund, max_letters, logic):
    count = 0
    while count < 100:
        premises = list()
        for num in range(number_premises):
            prem = random_propositional_formula(max_profund, max_letters, logic)
            premises.append(parse_propositional2(prem.replace(" ", ""), logic))
        concl = random_propositional_formula(max_profund, max_letters, logic)
        conclusion = parse_propositional2(concl.replace(" ", ""), logic)
        if max_letters > 1 and max_profund > 1:
            while conclusion in premises:
                concl = random_propositional_formula(max_profund, max_letters, logic)
                conclusion = parse_propositional2(concl.replace(" ", ""), logic)
        if is_valid(logic, conclusion, *premises):
            return[*premises, conclusion]
        count += 1
    raise ValueError("Could not find valid argument")


# ----------------------------------------------------------------------------------------------------------------------
# SEMANTIC DERIVATIONS
# have format {1: {'step': 1, 'formula': [formula], 'value': value, 'clause': '¬', 'on_steps': {steps} } ...}


def check_semantic_derivation(derivation, atomic_val, conclusion, logic):

    for step in sorted(derivation):
        if derivation[step]['clause'] == 'PREM':
            if derivation[step]['on_steps'] != set():
                return [step, "Premises must have empty 'on steps' field"]
            # See that the value is what atomic_val says
            entered = False
            for v in atomic_val:
                if v[0] == derivation[step]['formula'][0]:
                    entered = True
                    if derivation[step]['value'] != v[1]:
                        return[step, f"Incorrect value for the premise: Should be {v[1]}"]
            if not entered:
                return [step, f"The value of this formula was not given as premise"]

        else:
            # A rule is being applied
            # Get the constant
            constant = derivation[step]['clause']
            # See that the steps are between 0 and the current step
            for s in derivation[step]['on_steps']:
                if not (s > 0 and s < step):
                    return [step, "Incorrect 'on steps' specification"]


            # UNARY CONSTANT CLAUSE
            if constant in logic.constants(1):

                current_formula = derivation[step]['formula']
                current_value = derivation[step]['value']

                # Unary clauses always apply to 1 step
                if len(derivation[step]['on_steps']) != 1:
                    return [step, "Unary clauses apply to exactly one step"]

                prev_step = list(derivation[step]['on_steps'])[0]
                prev_formula = derivation[prev_step]['formula']
                prev_value = derivation[prev_step]['value']

                # If the current formula is the complex one
                if current_formula == [constant, prev_formula]:
                    true_value = logic.t_function(constant, prev_value)
                    if current_value != true_value:
                        return [step, f"Semantic clause was incorrectly applied: Value should be {true_value}"]

                # The premise is the complex one (e.g. v(°p)=1)
                elif prev_formula == [constant, current_formula]:
                    # See that the current value does give the prev value when the connective is applied
                    true_value = logic.t_function(constant, current_value)
                    if prev_value != true_value:
                        return [step, f"Semantic clause was incorrectly applied: Clause v{constant} applied to "
                                      f"{current_value} does not yield {prev_value}"]
                    # Also see that no other value gives the prev_value
                    other_values = [v for v in logic.values if v != current_value]
                    for v in other_values:
                        if logic.t_function(constant, v) == prev_value:
                            return[step, f"Semantic clause was incorrectly applied: Value {v} also yields {prev_value}"]

            # BINARY CONSTANT CLAUSE
            elif constant in logic.constants(2):
                # The cases where you give the two other valuations as premises
                if len(derivation[step]['on_steps']) == 2:
                    conclusion_formula = derivation[step]['formula']
                    conclusion_value = derivation[step]['value']
                    prev_steps = list(derivation[step]['on_steps'])
                    premise1_formula = derivation[prev_steps[0]]['formula']
                    premise1_value = derivation[prev_steps[0]]['value']
                    premise2_formula = derivation[prev_steps[1]]['formula']
                    premise2_value = derivation[prev_steps[1]]['value']

                    # Cases in which the conclusion is the complex formula
                    if conclusion_formula == [premise1_formula, constant, premise2_formula]:
                        true_value = logic.t_function(constant, premise1_value, premise2_value)
                        if conclusion_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Value should be {true_value}"]
                    elif conclusion_formula == [premise2_formula, constant, premise1_formula]:
                        true_value = logic.t_function(constant, premise2_value, premise1_value)
                        if conclusion_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Value should be {true_value}"]

                    # Cases in which the complex formula is in one of the premises (eg v(p v q)=1, v(p)=0 / v(q)=1)
                    # In this case try every other value for the conclusion formula and see if the given is unique
                    elif premise1_formula == [conclusion_formula, constant, premise2_formula]:
                        true_value = logic.t_function(constant, conclusion_value, premise2_value)
                        if premise1_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Clause v{constant} applied to "
                                          f"{conclusion_value} and {premise2_value} does not yield {premise1_value}"]
                        other_values = [v for v in logic.values if v != conclusion_value]
                        for v in other_values:
                            if logic.t_function(constant, v, premise2_value) == premise1_value:
                                return [step, f"Semantic clause was incorrectly applied: "
                                              f"Value {v} for this formula also yields {premise1_value}"]
                    elif premise1_formula == [premise2_formula, constant, conclusion_formula]:
                        true_value = logic.t_function(constant, premise2_value, conclusion_value)
                        if premise1_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Clause v{constant} applied to "
                                          f"{premise2_value} and {conclusion_value} does not yield {premise1_value}"]
                        other_values = [v for v in logic.values if v != conclusion_value]
                        for v in other_values:
                            if logic.t_function(constant, premise2_value, v) == premise1_value:
                                return [step, f"Semantic clause was incorrectly applied: "
                                              f"Value {v} for this formula also yields {premise1_value}"]
                    elif premise2_formula == [conclusion_formula, constant, premise1_formula]:
                        true_value = logic.t_function(constant, conclusion_value, premise1_value)
                        if premise2_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Clause v{constant} applied to "
                                          f"{conclusion_value} and {premise1_value} does not yield {premise2_value}"]
                        other_values = [v for v in logic.values if v != conclusion_value]
                        for v in other_values:
                            if logic.t_function(constant, v, premise1_value) == premise2_value:
                                return [step, f"Semantic clause was incorrectly applied: "
                                              f"Value {v} for this formula also yields {premise2_value}"]
                    elif premise2_formula == [premise1_formula, constant, conclusion_formula]:
                        true_value = logic.t_function(constant, premise1_value, conclusion_value)
                        if premise2_value != true_value:
                            return [step, f"Semantic clause was incorrectly applied: Clause v{constant} applied to "
                                          f"{premise1_value} and {conclusion_value} does not yield {premise2_value}"]
                        other_values = [v for v in logic.values if v != conclusion_value]
                        for v in other_values:
                            if logic.t_function(constant, premise1_value, v) == premise2_value:
                                return [step, f"Semantic clause was incorrectly applied: "
                                              f"Value {v} for this formula also yields {premise2_value}"]

                    # If none of the cases above, return an error
                    else:
                        return [step, f"Formulas given do not correspond with the clause utilized"]

                # The other cases, you give it only one premise
                elif len(derivation[step]['on_steps']) == 1:

                    conclusion_formula = derivation[step]['formula']
                    conclusion_value = derivation[step]['value']
                    prev_steps = list(derivation[step]['on_steps'])
                    premise_formula = derivation[prev_steps[0]]['formula']
                    premise_value = derivation[prev_steps[0]]['value']

                    # First two cases, the conclusion is the complex formula
                    # Check every other possible value for the second premise
                    if len(conclusion_formula) == 3 and conclusion_formula[1] == constant and \
                            conclusion_formula[0] == premise_formula:
                        # The other member of the formula is different
                        if conclusion_formula[2] != premise_formula:
                            for v in logic.values:
                                if logic.t_function(constant, premise_value, v) != conclusion_value:
                                    unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    other_formula = unparse_propositional_formula(conclusion_formula[2], logic)
                                    if other_formula[0] == '(' and other_formula[-1] == ')':
                                        other_formula = other_formula[1:-1]
                                    return [step, f"'On steps' given as input are not enough to warrant this inference:"
                                                  f" v({unp_premise_formula}) = {premise_value} and "
                                                  f"v({other_formula}) = {v} would yield a "
                                                  f"different value for the formula {unp_conclusion_formula}"]
                        # The other member is the same
                        else:
                            true_value = logic.t_function(constant, premise_value, premise_value)
                            if conclusion_value != true_value:
                                return [step, f"Clause incorrectly applied: Value should be {true_value}"]
                        # No need to repeat this bit in the next elif, if this is the case it will enter here
                    elif len(conclusion_formula) == 3 and conclusion_formula[1] == constant and \
                            conclusion_formula[2] == premise_formula:
                        for v in logic.values:
                            if logic.t_function(constant, v, premise_value) != conclusion_value:
                                unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                    unp_premise_formula = unp_premise_formula[1:-1]
                                unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                    unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                other_formula = unparse_propositional_formula(conclusion_formula[2], logic)
                                if other_formula[0] == '(' and other_formula[-1] == ')':
                                    other_formula = other_formula[1:-1]
                                return [step, f"'On steps' given as input are not enough to warrant this inference:"
                                              f"v({other_formula}) = {v} and "
                                              f"v({unp_premise_formula}) = {premise_value} would yield a "
                                              f"different value for the formula {unp_conclusion_formula}"]

                    # Second two cases, the premise is the complex formula (eg v(p & q) = 1 / v(p) = 1)
                    # For every possible value of the second premise, check that the complex value is the one given
                    # And that no other value for the premise given along with that other possible value yields the same
                    elif len(premise_formula) == 3 and premise_formula[1] == constant and \
                            premise_formula[0] == conclusion_formula:
                        # The other member of the binary formula is a different formula
                        if premise_formula[2] != conclusion_formula:
                            for premise2_value in logic.values:
                                if logic.t_function(constant, conclusion_value, premise2_value) != premise_value:
                                    premise2 = unparse_propositional_formula(premise_formula[2], logic)
                                    if premise2[0] == '(' and premise2[-1] == ')':
                                        premise2 = premise2[1:-1]
                                    unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    return [step, f"Inference is not warranted: "
                                                  f"if v({unp_conclusion_formula}) = {conclusion_value} and "
                                                  f"v({premise2}) = {premise2_value} then "
                                                  f"v({unp_premise_formula}) = {premise_value}"]
                                # Check that premise2_value and other possible values for concl value
                                # do not give the same result for prem1_value
                                other_values = [v for v in logic.values if v != conclusion_value]
                                for v in other_values:
                                    if logic.t_function(constant, v, premise2_value) == premise_value:
                                        premise2 = unparse_propositional_formula(premise_formula[2], logic)
                                        if premise2[0] == '(' and premise2[-1] == ')':
                                            premise2 = premise2[1:-1]
                                        unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                        if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                            unp_premise_formula = unp_premise_formula[1:-1]
                                        unp_conclusion_formula = unparse_propositional_formula(conclusion_formula,logic)
                                        if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                            unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                        return [step, f"Inference is not warranted: "
                                                      f"v({unp_conclusion_formula}) = {v} and "
                                                      f"v({premise2}) = {premise2_value} would yield "
                                                      f"the same value for {unp_premise_formula}"]
                        # It is the same formula
                        else:
                            if logic.t_function(constant, conclusion_value, conclusion_value) != premise_value:
                                return [step, f"Incorrect inference: {conclusion_value} and {conclusion_value} "
                                              f"do not yield {premise_value}"]
                            # Check that premise2_value and other possible values for concl value
                            # do not give the same result for prem1_value
                            other_values = [v for v in logic.values if v != conclusion_value]
                            for v in other_values:
                                if logic.t_function(constant, v, v) == premise_value:
                                    unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    return [step, f"Inference is not warranted: v({unp_conclusion_formula}) = {v} "
                                                  f"would yield the same value for {unp_premise_formula}"]
                    elif len(premise_formula) == 3 and premise_formula[1] == constant and \
                            premise_formula[2] == conclusion_formula:
                        for premise2_value in logic.values:
                            if logic.t_function(constant, premise2_value, conclusion_value) != premise_value:
                                premise2 = unparse_propositional_formula(premise_formula[2], logic)
                                if premise2[0] == '(' and premise2[-1] == ')':
                                    premise2 = premise2[1:-1]
                                unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                    unp_premise_formula = unp_premise_formula[1:-1]
                                unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                    unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                return [step, f"Inference is not warranted: "
                                              f"if v({premise2}) = {premise2_value} and "
                                              f"v({unp_conclusion_formula}) = {conclusion_value} then "
                                              f"v({unp_premise_formula}) = {premise_value}"]
                            # Check that premise2_value and other possible values for concl value
                            # do not give the same result for prem1_value
                            other_values = [v for v in logic.values if v != conclusion_value]
                            for v in other_values:
                                if logic.t_function(constant, premise2_value, v) == premise_value:
                                    premise2 = unparse_propositional_formula(premise_formula[2], logic)
                                    if premise2[0] == '(' and premise2[-1] == ')':
                                        premise2 = premise2[1:-1]
                                    unp_premise_formula = unparse_propositional_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_propositional_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    return [step, f"Inference is not warranted: "
                                                  f"v({premise2}) = {premise2_value} and "
                                                  f"v({unp_conclusion_formula}) = {v} would yield "
                                                  f"the same value for {unp_premise_formula}"]

                    # If none of the cases above, return an error
                    else:
                        return [step, f"Formulas given do not correspond with the clause utilized"]

                else:
                    return[step, "Incorrect number of steps specified (must be either 1 or 2)"]

            else:
                return[step, "Not a valid logical constant"]

    if derivation[len(derivation)]['formula'] != conclusion:
        return [len(derivation), "All rules are correctly applied but the conclusion is not the one seeked"]

    return []


def delete_repeated_lines(log):
    """Lines have format [step, [formula], value, clause, on_steps]"""
    log2 = list()
    # Start backwards
    for index1 in range(len(log)-1, 0, -1):
        # Then check forward until that index for the same formula
        for index2 in range(index1):
            if log[index1][1] == log[index2][1]:
                # If this happens then change the occurrences of index1 + 1 in on_steps for index2 + 1
                # Also subtract 1 from every on_steps greater than index1 + 1
                # And finally delete the line
                for index3 in range(index1 + 1, len(log)):
                    # Change every on_step that uses the repeated step for the previous one
                    for index4 in range(len(log[index3][4])):
                        if log[index3][4][index4] == index1 + 1:
                            log[index3][4].remove(index1 + 1)
                            log[index3][4].append(index2 + 1)
                            log[index3][4].sort()
                        # If it is greater than the repeated line, subtract one
                        elif log[index3][4][index4] > index1 + 1:
                            log[index3][4][index4] -= 1
                    # Subtract 1 to every step for the following ones
                    log[index3][0] -= 1
                del log[index1]
                break
    return log


def delete_unnecesary_lines(log):
    """There may be steps that are not used in a semantic derivation, deletes the unnecesary ones"""
    
    used_steps = register_steps(log, log[-1], used_steps=[log[-1][0]-1])
    used_steps = sorted(list(set(used_steps)))
    
    log = [log[x] for x in used_steps]
    
    return log

    
def register_steps(log, step, used_steps):
    
    for s in step[4]:
        used_steps.append(s-1)
        used_steps = register_steps(log, log[s-1], used_steps)
    
    return used_steps


def correct_on_steps(log):
    """After using the two functions above the on_steps are wrong, this function corrects them
    Just looks at the index where the step referred to is now located"""

    steps_list = [x[0] for x in log]

    for index in range(len(log)):
        for index2 in range(len(log[index][4])):
            prev_step = log[index][4][index2]
            new_step = steps_list.index(prev_step) + 1
            log[index][4][index2] = new_step

        # If a step has two repeated on_steps, delete one
        if len(log[index][4]) == 2 and log[index][4][0] == log[index][4][1]:
            log[index][4] = [log[index][4][0]]

    return log
