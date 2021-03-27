from copy import deepcopy
from itertools import product
from random import choice

try:
    from utils_formula_parser import FOL_individual_constants, FOL_predicates, FOL_variables, unparse_predicate_formula
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import FOL_individual_constants, FOL_predicates, FOL_variables, unparse_predicate_formula


# ----------------------------------------------------------------------------------------------------------------------
# derivations have format {1: {'step': 1, 'formula': [formula], 'value': value, 'clause': '¬', 'on_steps': {steps} }...}

def check_semantic_derivation(derivation, formula, model, logic):
    model_constants = {t for t in model if t in FOL_individual_constants}

    for step in sorted(derivation):

        # ATOMIC
        if derivation[step]['clause'] == 'vAtom':
            if len(derivation[step]['formula']) != 1:
                return [step, "The formula is not an atomic"]
            if derivation[step]['on_steps'] != set():
                return [step, "Premises must have empty 'on steps' field"]
            # See that the value is what the model says
            predicate = derivation[step]['formula'][0][0]
            if predicate + "+" not in model:
                return [step, f"Predicate {predicate} is not in the model"]
            predicate_extension = model[predicate + "+"]
            predicate_anti_extension = model[predicate + "-"]
            # Get the arity of the predicate
            # If both extension and antiextension are empty, check that the logic is K3 or L3 and that the value is i
            # or FDE and n
            if predicate_extension == list() and predicate_anti_extension == list():
                if (str(logic) == 'K3' or str(logic) == 'Ł3' or str(logic) == 'FDE') and \
                        (derivation[step]['value'] == 'i' or derivation[step]['value'] == 'n'):
                    pass
                else:
                    value = derivation[step]['value']
                    return[step, f"Incorrect value, should not be {value}"]

            else:
                complete_extension = predicate_extension[:]
                complete_extension.extend(predicate_anti_extension)
                if type(complete_extension[0]) == str:
                    arity = 1
                else:
                    arity = len(complete_extension[0])

                ind_constants = list(derivation[step]['formula'][0][1:])
                ind_denotations = tuple(model[x] for x in ind_constants)

                if arity == 1:
                    if len(ind_denotations) != 1:
                        return [step, "Predicate should have arity 1"]
                    if ind_denotations[0] in predicate_extension:
                        true_value = True
                    else:
                        true_value = False
                    if ind_denotations[0] in predicate_anti_extension:
                        false_value = True
                    else:
                        false_value = False

                # Arity greater than one
                else:
                    if len(ind_denotations) != arity:
                        return [step, f"Predicate should have arity {arity}"]
                    if ind_denotations in predicate_extension:
                        true_value = True
                    else:
                        true_value = False
                    if ind_denotations in predicate_anti_extension:
                        false_value = True
                    else:
                        false_value = False

                if true_value and not false_value:
                    correct_value = '1'
                elif false_value and not true_value:
                    correct_value = '0'
                elif not true_value and not false_value:
                    if 'i' in logic.values:
                        correct_value = 'i'
                    elif 'n' in logic.values:
                        correct_value = 'n'
                elif true_value and false_value:
                    if 'i' in logic.values:
                        correct_value = 'i'
                    elif 'b' in logic.values:
                        correct_value = 'b'

                if derivation[step]['value'] != correct_value:
                    return [step, f"Incorrect value, should be {correct_value}"]

        # A RULE IS BEING APPLIED
        else:
            # Get the constant
            constant = derivation[step]['clause']
            # See that the steps are between 0 and the current step
            for s in derivation[step]['on_steps']:
                if not 0 < s < step:
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
                            return [step,
                                    f"Semantic clause was incorrectly applied: Value {v} also yields {prev_value}"]

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
                                    unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    other_formula = unparse_predicate_formula(conclusion_formula[2], logic)
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
                                unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                    unp_premise_formula = unp_premise_formula[1:-1]
                                unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
                                if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                    unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                other_formula = unparse_predicate_formula(conclusion_formula[2], logic)
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
                                    premise2 = unparse_predicate_formula(premise_formula[2], logic)
                                    if premise2[0] == '(' and premise2[-1] == ')':
                                        premise2 = premise2[1:-1]
                                    unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
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
                                        premise2 = unparse_predicate_formula(premise_formula[2], logic)
                                        if premise2[0] == '(' and premise2[-1] == ')':
                                            premise2 = premise2[1:-1]
                                        unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                        if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                            unp_premise_formula = unp_premise_formula[1:-1]
                                        unp_conclusion_formula = unparse_predicate_formula(conclusion_formula,
                                                                                               logic)
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
                                    unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
                                    if unp_conclusion_formula[0] == '(' and unp_conclusion_formula[-1] == ')':
                                        unp_conclusion_formula = unp_conclusion_formula[1:-1]
                                    return [step, f"Inference is not warranted: v({unp_conclusion_formula}) = {v} "
                                                  f"would yield the same value for {unp_premise_formula}"]
                    elif len(premise_formula) == 3 and premise_formula[1] == constant and \
                            premise_formula[2] == conclusion_formula:
                        for premise2_value in logic.values:
                            if logic.t_function(constant, premise2_value, conclusion_value) != premise_value:
                                premise2 = unparse_predicate_formula(premise_formula[2], logic)
                                if premise2[0] == '(' and premise2[-1] == ')':
                                    premise2 = premise2[1:-1]
                                unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                    unp_premise_formula = unp_premise_formula[1:-1]
                                unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
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
                                    premise2 = unparse_predicate_formula(premise_formula[2], logic)
                                    if premise2[0] == '(' and premise2[-1] == ')':
                                        premise2 = premise2[1:-1]
                                    unp_premise_formula = unparse_predicate_formula(premise_formula, logic)
                                    if unp_premise_formula[0] == '(' and unp_premise_formula[-1] == ')':
                                        unp_premise_formula = unp_premise_formula[1:-1]
                                    unp_conclusion_formula = unparse_predicate_formula(conclusion_formula, logic)
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
                    return [step, "Incorrect number of steps specified (must be either 1 or 2)"]

            # QUANTIFIER CLAUSE
            elif constant in logic.quantifiers:
                current_formula = derivation[step]['formula']
                quantifier = current_formula[0]
                prev_steps = list(derivation[step]['on_steps'])

                if len(prev_steps) == 0:
                    return [step, "Number of steps must be greater than zero for the quantifiers' clauses to apply"]

                instances_present = set()
                universal_value = '1'
                existential_value = '0'
                for step2 in prev_steps:
                    prev_formula = derivation[step2]['formula']

                    # Check if the step is a quantifier introduction
                    instance_for_some_constant = False
                    for c in model_constants:
                        if prev_formula == substitute(current_formula[2], current_formula[1], c, logic):
                            instance_for_some_constant = True
                            instances_present.add(c)
                            break
                    if not instance_for_some_constant:
                        return [step, "Only quantifier introductions are allowed, "
                                      "and some previous formula is not an instance of this step's formula"]

                    universal_value = logic.t_function('˄', universal_value, derivation[step2]['value'])
                    existential_value = logic.t_function('˅', existential_value, derivation[step2]['value'])

                if quantifier == '∀':
                    if constant != quantifier:
                        return [step, "Formula is not an existential quantified one"]
                    # If the value put is either 1, all instances are needed
                    if derivation[step]['value'] != '0':
                        if instances_present != model_constants:
                            return [step, "All instances of a universal quantifier are necessary to introduce a "
                                          "true (or non-classical) value"]

                    if derivation[step]['value'] != universal_value:
                        if instances_present != model_constants:
                            return [step, "Insufficient information to conclude this. Check other instances"]
                        return [step, f"Incorrect value, should be {universal_value}"]

                elif quantifier == '∃':
                    if constant != quantifier:
                        return [step, "Formula is not a universally quantified one"]
                    # If the value put is in the false or non-classical values, all instances are needed
                    if derivation[step]['value'] != '1':
                        if instances_present != model_constants:
                            return [step, "All instances of an existential quantifier are necessary to introduce a "
                                          "false (or non-classical) value"]

                    if derivation[step]['value'] != existential_value:
                        if instances_present != model_constants:
                            return [step, "Insufficient information to conclude this. Check other instances"]
                        return [step, f"Incorrect value, should be {existential_value}"]

            else:
                # This should never happen but i'm leaving it here just in case
                return[step, "Not a valid logical constant"]

    if derivation[len(derivation)]['formula'] != formula:
        return [len(derivation), "All rules are correctly applied but the conclusion is not the one seeked"]

    return []

# ----------------------------------------------------------------------------------------------------------------------

def substitute(formula, variable, constant, logic):
    """Substitutes the free ocurrences of variable in formula for constant"""

    # Atomic
    if len(formula) == 1:
        return [formula[0].replace(variable, constant)]

    # Unary connective:
    if len(formula) == 2 and formula[0] in logic.constants(1):
        return [formula[0], substitute(formula[1], variable, constant, logic)]

    # Binary connective:
    if len(formula) == 3 and formula[1] in logic.constants(2):
        return [substitute(formula[0], variable, constant, logic), formula[1],
                substitute(formula[2], variable, constant, logic)]

    # Quantifier
    if len(formula) == 3 and formula[0] in logic.quantifiers:
        # If the variable is the same that is being replaced, do nothing
        if formula[1] == variable:
            return formula
        else:
            return [formula[0], formula[1], substitute(formula[2], variable, constant, logic)]


def valuation_model_log(formula, model, logic, counter=None):

    model_constants = [x for x in model if x in FOL_individual_constants]

    if counter is None:
        counter = 1

    # Atomic
    if len(formula) == 1:
        predicate = formula[0][0]
        predicate_extension = model[predicate + "+"]
        predicate_anti_extension = model[predicate + "-"]
        ind_constants = list(formula[0][1:])
        ind_denotations = tuple(model[x] for x in ind_constants)
        if len(ind_denotations) == 1:
            ind_denotations = ind_denotations[0]

        true_value = False
        false_value = False
        if ind_denotations in predicate_extension:
            true_value = True
        if ind_denotations in predicate_anti_extension:
            false_value = True

        if true_value and false_value:
            if 'i' in logic.values:
                val = 'i'
            elif 'b' in logic.values:
                val = 'b'
        elif true_value and not false_value:
            val = '1'
        elif false_value and not true_value:
            val = '0'
        elif not true_value and not false_value:
            if 'i' in logic.values:
                val = 'i'
            elif 'n' in logic.values:
                val = 'n'
        log = [[counter, formula, val, 'vAtom', []]]
        return [val, log]

    # Formula with unary connective
    if len(formula) == 2:
        inside_result = valuation_model_log(formula[1], model, logic, counter)
        inside_val = inside_result[0]
        log = inside_result[1]
        last_step = log[-1][0]

        val = logic.t_function(formula[0], inside_val)
        log.append([last_step + 1, formula, val, formula[0], [last_step]])
        counter += 1
        return [val, log]

    # Formula with binary connective
    if len(formula) == 3 and formula[1] in logic.constants(2):
        form1_result = valuation_model_log(formula[0], model, logic, counter)
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

        # If none of the above, check the value of the second formula
        form2_result = valuation_model_log(formula[2], model, logic, step1 + 1)
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

    # Formula with quantifier
    if len(formula) == 3 and formula[0] in logic.quantifiers:
        log = list()
        universal_value = '1'
        existential_value = '0'
        subst_val_steps = list()
        for c in sorted(model_constants):
            if log:
                last_step = log[-1][0]
            else:
                last_step = counter - 1
            subs_form = substitute(formula[2], formula[1], c, logic)
            result = valuation_model_log(subs_form, model, logic, last_step + 1)
            subst_val = result[0]
            log.extend(result[1])
            subst_val_steps.append(log[-1][0])

            universal_value = logic.t_function('˄', universal_value, subst_val)
            existential_value = logic.t_function('˅', existential_value, subst_val)

            # If the existential is 1 or the universal is 0, break before completing all substitutions
            if existential_value == '1' and formula[0] == '∃':
                log.append([subst_val_steps[-1] + 1, formula, existential_value, formula[0], [subst_val_steps[-1]]])
                return [existential_value, log]
            if universal_value == '0' and formula[0] == '∀':
                log.append([subst_val_steps[-1]+1, formula, universal_value, formula[0], [subst_val_steps[-1]]])
                return [universal_value, log]

        if formula[0] == '∀':
            log.append([subst_val_steps[-1]+1, formula, universal_value, formula[0], subst_val_steps])
            return [universal_value, log]
        elif formula[0] == '∃':
            log.append([subst_val_steps[-1]+1, formula, existential_value, formula[0], subst_val_steps])
            return [existential_value, log]

# ----------------------------------------------------------------------------------------------------------------------

def find_model(formulae, sought_value, logic):
    """Builds a model for a set of sentences. formulae is a list of parsed formulas"""

    domain = set()
    model = {'Domain': domain}

    # See how many constants and predicates there are
    constants = set()
    predicates = set()
    predicate_arity_dict = dict()
    for f in formulae:
        str_f = str(f)
        for index in range(len(str_f)):
            char = str_f[index]
            if char in FOL_individual_constants:
                constants.add(char)
            elif char in FOL_predicates:
                predicates.add(char)
                arity = 0
                for index2 in range(index+1, len(str_f)):
                    if str_f[index2] in FOL_individual_constants or str_f[index2] in FOL_variables:
                        arity += 1
                    else:
                        break
                predicate_arity_dict[char] = arity
    constants = sorted(list(constants))

    # Now add that many elements to the domain and their interpretations to the model
    for x in range(len(constants)):
        domain.add(str(x+1))
        model[constants[x]] = str(x+1)
    # If the domain is empty (the formulae contain no constants) add 1
    if not domain:
        domain.add('1')
        model['a'] = '1'
    # Add the predicates with empty extension and antiextension
    for pred in predicates:
        model[pred + "+"] = list()
        model[pred + "-"] = list()

    # Now try to find the model adding from 0 to 3 extra elements to the domain
    dom_cardinality = len(domain)
    for add_cts in range(4):
        domain.add(str(add_cts + dom_cardinality))
        if add_cts != 0:
            for ct in FOL_individual_constants:
                if ct not in model:
                    model[ct] = str(add_cts + dom_cardinality)
                    break

        try:
            requirements = [[form, sought_value] for form in formulae]  # The sought value is for each formula now
            model1 = dict()
            model1['Domain'] = model['Domain']
            for term in model:
                if type(model[term]) == str:
                    model1[term] = model[term]
                if type(model[term]) == list:
                    model1[term] = model[term][:]
            atomic_requirements = analyze_requirements(requirements, model1, logic)
            model = assign_model_predicates(model, atomic_requirements, logic, predicate_arity_dict)
            return model
        except ValueError:
            # If you already added 3 elements, or there were 3 or more constants
            # (much faster when the model does not exist)
            if dom_cardinality >= 3:
                break

    raise ValueError("Could not find model")


def analyze_requirements(requirements, model, logic, atomic_requirements=None):
    """Given the domain, analyzes the sentences for requirements and returns a model that satisfies them"""

    if atomic_requirements is None:
        atomic_requirements = {v: list() for v in logic.values}

    # Analyze the requirements for each sentence
    while requirements:
        sent_value = requirements[0]
        sent = sent_value[0]
        value = sent_value[1]

        # If atomic
        if len(sent) == 1:
            # Get the arity of the predicate, and the element or tuple of elements of the domain of the argument
            arity = len(sent[0]) - 1
            predicate = sent[0][0]
            constants = sent[0][1:]
            if len(constants) == 1:
                element = model[constants]
            else:
                element = tuple([model[c] for c in constants])

            # Analyze the sought value and what requirement follows from that
            for x in logic.values:
                if value == x:
                    # If contradiction in atomic requirements, raise ValueError
                    for y in set(logic.values) - {x}:
                        if [element, predicate] in atomic_requirements[y]:
                            raise ValueError("Contradiction in atomic requirements")
                    if [element, predicate] not in atomic_requirements[x]:
                        atomic_requirements[x].append([element, predicate])
                        break
            del requirements[0]

        # If unary constant
        elif len(sent) == 2 and sent[0] in logic.constants(1):
            constant = sent[0]
            sent_form = sent[1]
            del requirements[0]

            # Look at the t function for the constant to see which values of sent_form give value
            for v in logic.values:
                if logic.t_function(constant, v) == value:
                    requirements.insert(0, [sent_form, v])
                    try:
                        # Make copies so that the originals are not modified at each value tried
                        requirements1 = deepcopy(requirements)
                        atomic_requirements1 = {x: atomic_requirements[x][:] for x in atomic_requirements}
                        atomic_requirements = analyze_requirements(requirements1, model, logic, atomic_requirements1)
                        return atomic_requirements
                    except ValueError:
                        del requirements[0]

            # If you got out of the previous loop and did not return, the requirement is unsatisfiable
            raise ValueError("Unsatisfiable unary requirement")

        # If binary constant
        elif len(sent) == 3 and sent[1] in logic.constants(2):
            constant = sent[1]
            sent1 = sent[0]
            sent2 = sent[2]
            del requirements[0]

            # Look at the t function for the constant to see which values of sent_form give value
            for v1 in logic.values:
                for v2 in logic.values:
                    if logic.t_function(constant, v1, v2) == value:
                        requirements.insert(0, [sent1, v1])
                        requirements.insert(0, [sent2, v2])

                        try:
                            # Make copies so that the originals are not modified at each value tried
                            requirements1 = deepcopy(requirements)
                            atomic_requirements1 = {x: atomic_requirements[x][:] for x in atomic_requirements}
                            atomic_requirements = analyze_requirements(requirements1, model, logic, atomic_requirements1)
                            return atomic_requirements
                        except ValueError:
                            del requirements[0]
                            del requirements[0]

            # If you got out of the previous loop and did not return, the requirement is unsatisfiable
            raise ValueError("Unsatisfiable binary requirement")

        # If quantifier
        elif len(sent) == 3 and sent[0] in logic.quantifiers:
            quantifier = sent[0]
            variable = sent[1]
            sent1 = sent[2]
            model_cts = [x for x in model if x in FOL_individual_constants]
            del requirements[0]

            # Get every instance
            instances = list()
            for c in model_cts:
                instances.append(substitute(sent1, variable, c, logic))

            # Get every possible combination of values for the instances
            possible_value_combinations = list(product(logic.values, repeat=len(instances)))

            for value_comb in possible_value_combinations:
                v = value_comb[0]
                for v2 in value_comb[1:]:
                    if quantifier == '∃':
                        v = logic.t_function('˅', v, v2)
                    if quantifier == '∀':
                        v = logic.t_function('˄', v, v2)

                if v == value:
                    new_requirements = [[instances[x], value_comb[x]] for x in range(len(instances))]
                    requirements1 = deepcopy(requirements)
                    requirements1.extend(new_requirements)
                    try:
                        atomic_requirements1 = {x: atomic_requirements[x][:] for x in atomic_requirements}
                        atomic_requirements = analyze_requirements(requirements1, model, logic, atomic_requirements1)
                        return atomic_requirements
                    except ValueError:
                        pass

            # If you got out of the previous loop and did not return, the requirement is unsatisfiable
            raise ValueError("Unsatisfiable quantifier requirement")

    return atomic_requirements


def assign_model_predicates(model, atomic_requirements, logic, predicate_arity_dict):

    all_requirements = atomic_requirements['0'][:]
    all_requirements.extend(atomic_requirements['1'][:])
    if 'i' in atomic_requirements:
        all_requirements.extend(atomic_requirements['i'][:])
    if 'n' in atomic_requirements:
        all_requirements.extend(atomic_requirements['n'][:])
        all_requirements.extend(atomic_requirements['b'][:])

    # 0 and 1 requirements assign them to the anti-extension and extension, respectively
    for req in atomic_requirements['0']:
        model[req[1] + "-"].append(req[0])
    for req in atomic_requirements['1']:
        model[req[1] + "+"].append(req[0])
    # i requirements, check the logic. If paracomplete, do nothing, if paraconsistent assign to both
    if 'i' in atomic_requirements:
        for req in atomic_requirements['i']:
            if str(logic) == 'LP' or str(logic) == 'RM3':
                model[req[1] + "-"].append(req[0])
                model[req[1] + "+"].append(req[0])
    # b requirements, assign to both (n, do nothing)
    if 'b' in atomic_requirements:
        for req in atomic_requirements['b']:
            model[req[1] + "-"].append(req[0])
            model[req[1] + "+"].append(req[0])

    # With this, requirements are satisfied
    # Now, we must check the rest of the arguments for which there is no requirement
    for pred in predicate_arity_dict:
        arity = predicate_arity_dict[pred]
        if arity == 1:
            possible_elements = list(model["Domain"].copy())
        else:
            possible_elements = list(product(model["Domain"].copy(), repeat=arity))

        for req in all_requirements:
            if req[1] == pred:
                possible_elements.remove(req[0])

        # Possible elements now contains the elements for which there is no requirement
        for elem in possible_elements:
            # If the logic is classical, put them either in the extension or anti-extension
            if str(logic) == 'Classical':
                if choice((True, False)):
                    model[pred + '+'].append(elem)
                else:
                    model[pred + '-'].append(elem)
            # If the logic is paracomplete, add in ext, anti-ext or neither
            if str(logic) == 'K3' or str(logic) == 'Ł3':
                put_in = choice(['ext', 'antiext', 'neither'])
                if put_in == 'ext':
                    model[pred + '+'].append(elem)
                if put_in == 'antiext':
                    model[pred + '-'].append(elem)
            # If the logic is paraconsistent, add in ext, anti-ext or both
            if str(logic) == 'LP' or str(logic) == 'FDE':
                put_in = choice(['ext', 'antiext', 'both'])
                if put_in == 'ext':
                    model[pred + '+'].append(elem)
                if put_in == 'antiext':
                    model[pred + '-'].append(elem)
                if put_in == 'both':
                    model[pred + '+'].append(elem)
                    model[pred + '-'].append(elem)
            # If FDE, in ext, antiext, both or neither
            if str(logic) == 'FDE':
                put_in = choice(['ext', 'antiext', 'both', 'neither'])
                if put_in == 'ext':
                    model[pred + '+'].append(elem)
                if put_in == 'antiext':
                    model[pred + '-'].append(elem)
                if put_in == 'both':
                    model[pred + '+'].append(elem)
                    model[pred + '-'].append(elem)

    return model


# ----------------------------------------------------------------------------------------------------------------------

model_finding_preset_excercises = [
    ['Pa, ¬Qb', '1'],
    ['¬Rab ˅ Qa', '0'],
    ['∃x Px, ∃y ¬Py', '1'],
    ['∃x Px, Qa', '0'],
    ['¬∀x ¬Px, ¬Pa', '1'],
    ['∀x Px → ∀x Qx', '0'],
    ['∀x ¬Rxx, ∀x ∀y (Rxy → Ryx), Rcb', '1'],
    ['∀x ∃y Rxy, ¬∃y ∀x Rxy', '1'],
    ['∀x ∀y (Rxy → ¬Ryx), Rab, Rcb', '1'],
    ['¬∀x Rxx, ∀x ∀y (Rxy → ¬Ryx), ¬∀x ∃y Rxy', '0']
]
