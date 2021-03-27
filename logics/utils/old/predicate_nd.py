try:
    from utils_formula_parser import FOL_individual_constants
    from utils_logic_class import Classical2
    from utils_models import substitute
    from utils_natural_deduction import add_open_sups, register_steps, numerate_on_steps
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import FOL_individual_constants
    from exercises.templates.exercises.utils_logic_class import Classical2
    from exercises.templates.exercises.utils_models import substitute
    from exercises.templates.exercises.utils_natural_deduction import add_open_sups, register_steps, numerate_on_steps


def solve_derivation(premises, conclusion, non_arbitrary_cts=None, existentials_tried_indexes=None):

    if non_arbitrary_cts is None:
        non_arbitrary_cts = list({x for x in FOL_individual_constants for p in premises if x in str(p)})
    if existentials_tried_indexes is None:
        existentials_tried_indexes = list()

    derivation = [[x[:], 'PREM', []] for x in premises]
    goal = conclusion

    while True:
        # Apply simplification rules (elimination + a couple more)
        derivation = apply_simplification_rules(derivation, goal)
        formulas_list = [x[0] for x in derivation]
        untried_existentials_indexes_list = [formulas_list.index(x) for x in formulas_list if x[0] == '∃' and
                                             formulas_list.index(x) not in existentials_tried_indexes]

        # The goal has been reached
        if goal in formulas_list:
            if derivation[-1][0] != goal:
                derivation.append([goal, 'REP', [goal]])
            return derivation

        # If Falsum is in the derivation apply EFSQ
        elif ['⊥'] in [x[0] for x in derivation]:
            derivation.append([goal, 'EFSQ', [['⊥']]])
            return derivation

        # If you have an existential that you have not tried to eliminate yet, do it
        elif untried_existentials_indexes_list:
            existentials_tried_indexes.append(untried_existentials_indexes_list[0])
            cts_in_goal = {x for x in str(goal) if x in FOL_individual_constants}
            non_arbitrary_cts.extend(cts_in_goal)
            arbitrary_cts = [x for x in FOL_individual_constants if x not in non_arbitrary_cts]
            if arbitrary_cts:
                prems = [x[0] for x in derivation]
                existential_to_substitute = derivation[untried_existentials_indexes_list[0]][0]
                subst_inst = substitute(existential_to_substitute[2], existential_to_substitute[1], arbitrary_cts[0],
                                        Classical2)
                prems.append(subst_inst)
                non_arbitrary_cts.append(arbitrary_cts[0])
                deriv = solve_derivation(prems, goal, non_arbitrary_cts, existentials_tried_indexes)
                del non_arbitrary_cts[-1]
                if cts_in_goal:
                    non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

                derivation.append([subst_inst, 'SUP', []])
                derivation.extend([x for x in deriv if x[1] != 'PREM'])
                derivation.append([[subst_inst, "→", goal], "I→", [subst_inst, goal]])
                derivation.append([goal, "E∃", [existential_to_substitute, [subst_inst, "→", goal]]])
                return derivation

            if cts_in_goal:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

        # If the goal is Falsum, and the simplification rules did not provide it, raise an error
        elif goal == ['⊥']:
            raise ValueError("Goal is ⊥ and elimination rules did not resolve the derivation")

        # If the goal is an atomic, try reductio
        elif len(goal) == 1:
            prems = [x[0] for x in derivation]
            prems.append(['¬', goal])

            # Add non-arbitrary constants
            cts_in_goal = {x for x in str(goal) if x in FOL_individual_constants}
            if cts_in_goal:
                non_arbitrary_cts.extend(list(cts_in_goal))

            deriv = solve_derivation(prems, ['⊥'], non_arbitrary_cts, existentials_tried_indexes)

            # Remove non-arbitrary constants
            if cts_in_goal:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

            derivation.append([['¬', goal], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
            derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
            return derivation

        # If the goal is a negation, try reductio
        elif len(goal) == 2 and goal[0] == '¬':
            prems = [x[0] for x in derivation]
            prems.append(goal[1])

            cts_in_goal = {x for x in str(goal[1]) if x in FOL_individual_constants}
            if cts_in_goal:
                non_arbitrary_cts.extend(list(cts_in_goal))
            deriv = solve_derivation(prems, ['⊥'], non_arbitrary_cts, existentials_tried_indexes)
            if cts_in_goal:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

            derivation.append([goal[1], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([goal, "I¬", [goal[1], ['⊥']]])
            return derivation

        # If the goal is a conjunction, make two derivations of both conjuncts
        elif len(goal) == 3 and goal[1] == '˄':
            prems = [x[0] for x in derivation]
            deriv1 = solve_derivation(prems, goal[0], non_arbitrary_cts, existentials_tried_indexes)
            deriv2 = solve_derivation(prems, goal[2], non_arbitrary_cts, existentials_tried_indexes)

            derivation.extend([x for x in deriv1 if x[1] != 'PREM'])
            derivation.extend([x for x in deriv2 if x[1] != 'PREM'])
            derivation.append([goal, "I˄", [goal[0], goal[2]]])

            return derivation

        # If the goal is a conditional, take the antecedent as premise and set as goal the conclusion
        elif len(goal) == 3 and goal[1] == '→':
            prems = [x[0] for x in derivation]
            prems.append(goal[0])

            cts_in_antecedent = {x for x in str(goal[0]) if x in FOL_individual_constants}
            if cts_in_antecedent:
                non_arbitrary_cts.extend(list(cts_in_antecedent))
            deriv = solve_derivation(prems, goal[2], non_arbitrary_cts, existentials_tried_indexes)
            if cts_in_antecedent:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_antecedent)]

            derivation.append([goal[0], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([goal, "I→", [goal[0], goal[2]]])
            return derivation

        # If the goal is a disjunction, try to derive each disjunct separately
        # If that fails, try reductio
        elif len(goal) == 3 and goal[1] == '˅':
            prems = [x[0] for x in derivation]
            try:
                deriv = solve_derivation(prems, goal[0], non_arbitrary_cts, existentials_tried_indexes)
                derivation.extend([x for x in deriv if x[1] != 'PREM'])
                derivation.append([goal, 'I˅', [goal[0]]])
                return derivation
            except ValueError:
                try:
                    deriv = solve_derivation(prems, goal[2], non_arbitrary_cts, existentials_tried_indexes)
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([goal, 'I˅', [goal[2]]])
                    return derivation
                except ValueError:
                    prems.append(['¬', goal])

                    cts_in_goal = {x for x in str(goal[1]) if x in FOL_individual_constants}
                    if cts_in_goal:
                        non_arbitrary_cts.extend(list(cts_in_goal))
                    deriv = solve_derivation(prems, ['⊥'], non_arbitrary_cts, existentials_tried_indexes)
                    if cts_in_goal:
                        non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

                    derivation.append([['¬', goal], 'SUP', []])
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
                    derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
                    return derivation

        # If the goal is an existential quantifier, act similarly to disjunction
        # First try to derive each of the substitution instances of the letters present, +1 arbitrary one
        # If that fails, try reductio
        elif len(goal) == 3 and goal[0] == '∃':
            prems = [x[0] for x in derivation]
            letters_present = [x for p in prems for x in str(p) if x in FOL_individual_constants]
            arbitrary_cts = [x for x in FOL_individual_constants if x not in letters_present]
            if arbitrary_cts:
                letters_present.append(arbitrary_cts[0])
            for c in letters_present:
                subst_instance = substitute(goal[2], goal[1], c, Classical2)
                try:
                    deriv = solve_derivation(prems, subst_instance, non_arbitrary_cts, existentials_tried_indexes)
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([goal, 'I∃', [subst_instance]])
                    return derivation
                except ValueError:
                    pass

            # If you got to here, try reductio
            prems.append(['¬', goal])

            cts_in_goal = {x for x in str(goal[1]) if x in FOL_individual_constants}
            if cts_in_goal:
                non_arbitrary_cts.extend(list(cts_in_goal))
            deriv = solve_derivation(prems, ['⊥'], non_arbitrary_cts, existentials_tried_indexes)
            if cts_in_goal:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

            derivation.append([['¬', goal], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
            derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
            return derivation

        # If the goal is a universal quantifier, try to derive each arbitrary constant substitution
        # If that fails, try reductio
        elif len(goal) == 3 and goal[0] == '∀':
            prems = [x[0] for x in derivation]
            arbitrary_cts = [x for x in FOL_individual_constants if x not in non_arbitrary_cts]
            for c in arbitrary_cts:
                subst_instance = substitute(goal[2], goal[1], c, Classical2)
                non_arbitrary_cts.append(c)
                try:
                    deriv = solve_derivation(prems, subst_instance, non_arbitrary_cts, existentials_tried_indexes)
                    del non_arbitrary_cts[-1]
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([goal, "I∀", [subst_instance]])
                    return derivation
                except ValueError:
                    del non_arbitrary_cts[-1]

            # If you got to here, try reductio
            prems.append(['¬', goal])

            cts_in_goal = {x for x in str(goal[1]) if x in FOL_individual_constants}
            if cts_in_goal:
                non_arbitrary_cts.extend(list(cts_in_goal))
            deriv = solve_derivation(prems, ['⊥'], non_arbitrary_cts, existentials_tried_indexes)
            if cts_in_goal:
                non_arbitrary_cts = non_arbitrary_cts[:-len(cts_in_goal)]

            derivation.append([['¬', goal], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
            derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
            return derivation

        else:
            raise ValueError("This should not happen")


def apply_simplification_rules(derivation, goal):
    """Makes changes and records the indexes on applied_rules (so that it doesn't repeat them)
    When it has no more changes to make (modif = False), returns"""

    applied_rules = {'E˄': [], 'E→': [], 'MT': [], 'E˅': [], 'DN': [],
                     'DM': [], 'DM2': [], 'NegCond': [], 'E¬': [], 'SD': [], 'E∀': [], 'NegExist': [], 'NegUniv': []}
    while True:
        modif = False
        formulas_list = [x[0] for x in derivation]
        formulas_list2 = formulas_list[:]
        for formula in formulas_list:

            # Conjunction elimination
            if len(formula) == 3 and formula[1] == '˄':
                if formulas_list.index(formula) not in applied_rules['E˄']:
                    if formula[0] not in formulas_list2:
                        formulas_list2.append(formula[0])
                        derivation.append([formula[0], "E˄", [formula]])
                        if goal == formula[0]:
                            return derivation
                    if formula[2] not in formulas_list2:
                        formulas_list2.append(formula[2])
                        derivation.append([formula[2], "E˄", [formula]])
                        if goal == formula[2]:
                            return derivation
                    applied_rules['E˄'].append(formulas_list.index(formula))
                    modif = True

            # Conditional elimination and MT
            elif len(formula) == 3 and formula[1] == '→':
                for formula2 in formulas_list:
                    if formula[0] == formula2:
                        if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['E→']:
                            if formula[2] not in formulas_list2:
                                formulas_list2.append(formula[2])
                                derivation.append([formula[2], "E→", [formula, formula2]])
                                if goal == formula[2]:
                                    return derivation
                            applied_rules['E→'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                            modif = True
                    # Independent formula might be the negation of the consequent OR VICE VERSA (p then ¬q, q / ¬p)
                    elif formula2 == ['¬', formula[2]] or formula[2] == ['¬', formula2]:
                        if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['MT']:
                            if ['¬', formula[0]] not in formulas_list2:
                                formulas_list2.append(['¬', formula[0]])
                                derivation.append([['¬', formula[0]], "MT", [formula, formula2]])
                                if goal == ['¬', formula[0]]:
                                    return derivation
                            applied_rules['MT'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                            modif = True

            # Disjunction elimination and SD
            elif len(formula) == 3 and formula[1] == '˅':
                # See if it can find the first conditional
                for formula2 in formulas_list:
                    if len(formula2) == 3 and formula2[1] == '→' and formula2[0] == formula[0]:
                        consequent = formula2[2]
                        # Try and find the second conditional
                        for formula3 in formulas_list:
                            if len(formula3) == 3 and formula3[1] == '→' and \
                                    formula3[0] == formula[2] and formula3[2] == consequent:
                                if (formulas_list.index(formula), formulas_list.index(formula2),
                                        formulas_list.index(formula3)) not in applied_rules['E˅']:
                                    if consequent not in formulas_list2:
                                        formulas_list2.append(consequent)
                                        derivation.append([consequent, "E˅", [formula, formula2, formula3]])
                                        if goal == consequent:
                                            return derivation
                                    applied_rules['E˅'].append((formulas_list.index(formula),
                                                                formulas_list.index(formula2),
                                                                formulas_list.index(formula3)))
                                    modif = True
                    # SD - Formula2 is the negation of the first disjunct
                    if formula[0] == ['¬', formula2] or ['¬', formula[0]] == formula2:
                        if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['SD']:
                            if formula[2] not in formulas_list2:
                                formulas_list2.append(formula[2])
                                derivation.append([formula[2], 'SD', [formula, formula2]])
                                if goal == formula[2]:
                                    return derivation
                            applied_rules['SD'].append((formulas_list.index(formula),
                                                        formulas_list.index(formula2)))
                            modif = True
                    # SD - Formula2 is the negation of the second disjunct
                    if formula[2] == ['¬', formula2] or ['¬', formula[2]] == formula2:
                        if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['SD']:
                            if formula[0] not in formulas_list2:
                                formulas_list2.append(formula[0])
                                derivation.append([formula[0], 'SD', [formula, formula2]])
                                if goal == formula[0]:
                                    return derivation
                            applied_rules['SD'].append((formulas_list.index(formula),
                                                        formulas_list.index(formula2)))
                            modif = True

            # Universal quantifier elimination
            if len(formula) == 3 and formula[0] == '∀':
                if formulas_list.index(formula) not in applied_rules['E∀']:
                    for c in FOL_individual_constants:
                        subst_instance = substitute(formula[2], formula[1], c, Classical2)
                        if subst_instance == goal:
                            formulas_list2.append(subst_instance)
                            derivation.append([subst_instance, "E∀", [formula]])
                            return derivation
                        if subst_instance not in formulas_list2:
                            formulas_list2.append(subst_instance)
                            derivation.append([subst_instance, "E∀", [formula]])
                    applied_rules['E∀'].append(formulas_list.index(formula))
                    modif = True

            # The formula is a negation
            elif len(formula) == 2 and formula[0] == '¬':
                negated_formula = formula[1]
                # If negating a negation, apply DN
                if len(negated_formula) == 2 and negated_formula[0] == '¬':
                    if formulas_list.index(formula) not in applied_rules['DN']:
                        if negated_formula[1] not in formulas_list2:
                            formulas_list2.append(negated_formula[1])
                            derivation.append([negated_formula[1], "DN", [formula]])
                            if goal == negated_formula[1]:
                                return derivation
                        applied_rules['DN'].append(formulas_list.index(formula))
                        modif = True
                # If negating a disjunction, apply DeMorgan
                if len(negated_formula) == 3 and negated_formula[1] == '˅':
                    if formulas_list.index(formula) not in applied_rules['DM']:
                        if ['¬', negated_formula[0]] not in formulas_list2:
                            formulas_list2.append(['¬', negated_formula[0]])
                            derivation.append([['¬', negated_formula[0]], "DM", [formula]])
                            if goal == ['¬', negated_formula[0]]:
                                return derivation
                        if ['¬', negated_formula[2]] not in formulas_list2:
                            formulas_list2.append(['¬', negated_formula[2]])
                            derivation.append([['¬', negated_formula[2]], "DM", [formula]])
                            if goal == ['¬', negated_formula[2]]:
                                return derivation
                        applied_rules['DM'].append(formulas_list.index(formula))
                        modif = True
                # If negating a conjunction, apply DeMorgan2
                if len(negated_formula) == 3 and negated_formula[1] == '˄':
                    if formulas_list.index(formula) not in applied_rules['DM2']:
                        if [['¬', negated_formula[0]], '˅', ['¬', negated_formula[2]]] not in formulas_list2:
                            formulas_list2.append([['¬', negated_formula[0]], '˅', ['¬', negated_formula[2]]])
                            derivation.append([[['¬', negated_formula[0]], '˅', ['¬', negated_formula[2]]],
                                               "DM2", [formula]])
                            if goal == [['¬', negated_formula[0]], '˅', ['¬', negated_formula[2]]]:
                                return derivation
                        applied_rules['DM2'].append(formulas_list.index(formula))
                        modif = True
                # If negating a conditional, apply NegCond
                elif len(negated_formula) == 3 and negated_formula[1] == '→':
                    if formulas_list.index(formula) not in applied_rules['NegCond']:
                        if negated_formula[0] not in formulas_list2:
                            formulas_list2.append(negated_formula[0])
                            derivation.append([negated_formula[0], "NegCond", [formula]])
                            if goal == negated_formula[0]:
                                return derivation
                        if ['¬', negated_formula[2]] not in formulas_list2:
                            formulas_list2.append(['¬', negated_formula[2]])
                            derivation.append([['¬', negated_formula[2]], "NegCond", [formula]])
                            if goal == ['¬', negated_formula[2]]:
                                return derivation
                        applied_rules['NegCond'].append(formulas_list.index(formula))
                        modif = True
                # If negating a universal quantifier, apply NegUniv
                elif len(negated_formula) == 3 and negated_formula[0] == '∀':
                    if formulas_list.index(formula) not in applied_rules['NegUniv']:
                        formula_quantified = negated_formula[2]
                        new_formula = ['∃', negated_formula[1], ['¬', formula_quantified]]
                        if new_formula not in formulas_list2:
                            formulas_list2.append(new_formula)
                            derivation.append([new_formula, "NegUniv", [formula]])
                            if goal == new_formula:
                                return derivation
                        applied_rules['NegUniv'].append(formulas_list.index(formula))
                        modif = True
                # If negating a universal quantifier, apply NegExist
                elif len(negated_formula) == 3 and negated_formula[0] == '∃':
                    if formulas_list.index(formula) not in applied_rules['NegExist']:
                        formula_quantified = negated_formula[2]
                        new_formula = ['∀', negated_formula[1], ['¬', formula_quantified]]
                        if new_formula not in formulas_list2:
                            formulas_list2.append(new_formula)
                            derivation.append([new_formula, "NegExist", [formula]])
                            if goal == new_formula:
                                return derivation
                        applied_rules['NegExist'].append(formulas_list.index(formula))
                        modif = True
                # See if you can apply E¬
                for formula2 in formulas_list:
                    # If the two formulas are contradictory, derive Falsum
                    if formula2 == negated_formula:
                        if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['E¬']:
                            if ['⊥'] not in formulas_list2:
                                formulas_list2.append(['⊥'])
                                derivation.append([['⊥'], "E¬", [formula, formula2]])
                                if goal == ['⊥']:
                                    return derivation
                            applied_rules['E¬'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                            modif = True
        if not modif:
            return derivation


# ----------------------------------------------------------------------------------------------------------------------

def make_derivation_pretty(derivation):
    """Enumerates the steps, deletes unnecessary lines, etc."""

    # First, add the open_sups as a fourth list in each step
    derivation = add_open_sups(derivation)

    # Second, delete the steps that are never used
    used_steps = register_steps(derivation, derivation[-1], len(derivation) - 1, [len(derivation) - 1])
    prem_steps = [x for x in derivation if x[1] == 'PREM']
    prem_indexes = [derivation.index(x) for x in prem_steps]
    used_steps.extend(prem_indexes)
    used_steps = list(set(used_steps))  # Remove repetitions from used_steps
    used_steps.sort()  # Order them
    derivation = [derivation[index] for index in used_steps]

    # Third, replace the derived rules with their hardcoded demonstration
    derivation = replace_derived_rules(derivation)

    # Lastly, replace the on_steps with numbers and add necessary REP steps
    derivation = numerate_on_steps(derivation)

    return derivation


def replace_derived_rules(derivation):
    """Replaces DM, DM2, NegCond, MT, SD with their hardcoded derivation"""

    derivation2 = list()
    formulas_list = [x[0] for x in derivation]
    cts_used = {x for f in formulas_list for x in FOL_individual_constants if x in str(f)}
    cts_unused = list(set(FOL_individual_constants) - cts_used)

    # In the first pass it replaces only DM2 (since DM2 uses DM)
    for step in range(len(derivation)):
        step_open_sups = derivation[step][3]
        if derivation[step][1] == "DM2":
            # A DM2 step has structure [ [[¬, [p]], or, [¬, [q]]], 'DM2', [[¬, [[p], & [q]]]] ]
            negated_conjunction = derivation[step][2][0]
            disjunction = derivation[step][0]

            new_steps = list()
            step_open_sups.append(['¬', disjunction])
            new_steps.append([['¬', disjunction], 'SUP', [], step_open_sups[:]])
            new_steps.append([['¬', disjunction[0]], 'DM', [['¬', disjunction]], step_open_sups[:]])
            new_steps.append([['¬', disjunction[2]], 'DM', [['¬', disjunction]], step_open_sups[:]])
            new_steps.append([disjunction[0][1], 'DN', [['¬', disjunction[0]]], step_open_sups[:]])
            new_steps.append([disjunction[2][1], 'DN', [['¬', disjunction[2]]], step_open_sups[:]])
            new_steps.append([negated_conjunction[1], 'I˄', [disjunction[0][1], disjunction[2][1]], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [negated_conjunction, negated_conjunction[1]], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([['¬', ['¬', disjunction]], 'I¬', [['¬', disjunction], ['⊥']], step_open_sups[:]])
            new_steps.append([disjunction, 'DN', [['¬', ['¬', disjunction]]], step_open_sups[:]])
            derivation2.extend(new_steps)

        else:
            derivation2.append(derivation[step])

    derivation3 = list()

    # Second pass: The rest of the rules
    for step in range(len(derivation2)):
        step_open_sups = derivation2[step][3]
        if derivation2[step][1] == "DM":
            # A DM steps looks like [ [¬,[p]], DM, [[¬,[[p] v [q]]]] ] or like [ [¬,[q]], DM, [[¬,[[p] v [q]]]] ]
            negated_disjunct = derivation2[step][0]
            disjunct = negated_disjunct[1]
            negated_disjunction = derivation2[step][2][0]
            disjunction = negated_disjunction[1]

            new_steps = list()
            step_open_sups.append(disjunct)
            new_steps.append([disjunct, 'SUP', [], step_open_sups[:]])
            new_steps.append([disjunction, 'I˅', [disjunct], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [negated_disjunction, disjunction], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([negated_disjunct, 'I¬', [disjunct, ['⊥']], step_open_sups[:]])
            derivation3.extend(new_steps)

        elif derivation2[step][1] == "NegCond":
            # A NegCond step looks either like:
            # [ [p], NegCond, [[¬, [[p], then, [q]]]] ] or
            # [ [¬, [q]], NegCond, [[¬, [[p], then, [q]]]] ]

            negated_conditional = derivation2[step][2][0]
            conditional = negated_conditional[1]
            antecedent = conditional[0]
            consequent = conditional[2]

            if derivation2[step][0] == antecedent:

                new_steps = list()
                step_open_sups.append(['¬', antecedent])
                new_steps.append([['¬', antecedent], 'SUP', [], step_open_sups[:]])
                step_open_sups.append(antecedent)
                new_steps.append([antecedent, 'SUP', [], step_open_sups[:]])
                new_steps.append([['⊥'], 'E¬', [['¬', antecedent], antecedent], step_open_sups[:]])
                new_steps.append([consequent, 'EFSQ', [['⊥']], step_open_sups[:]])
                del step_open_sups[-1]
                new_steps.append([conditional, 'I→', [antecedent, consequent], step_open_sups[:]])
                new_steps.append([['⊥'], 'E¬', [negated_conditional, conditional], step_open_sups[:]])
                del step_open_sups[-1]
                new_steps.append([['¬', ['¬', antecedent]], 'I¬', [['¬', antecedent], ['⊥']], step_open_sups[:]])
                new_steps.append([antecedent, 'DN', [['¬', ['¬', antecedent]]], step_open_sups[:]])
                derivation3.extend(new_steps)

            elif derivation2[step][0] == ['¬', consequent]:
                new_steps = list()
                step_open_sups.append(consequent)
                new_steps.append([consequent, 'SUP', [], step_open_sups[:]])
                step_open_sups.append(antecedent)
                new_steps.append([antecedent, 'SUP', [], step_open_sups[:]])
                new_steps.append([consequent, 'REP', [consequent], step_open_sups[:]])
                del step_open_sups[-1]
                new_steps.append([conditional, 'I→', [consequent, antecedent], step_open_sups[:]])
                new_steps.append([['⊥'], 'E¬', [conditional, negated_conditional], step_open_sups[:]])
                del step_open_sups[-1]
                new_steps.append([['¬', consequent], 'I¬', [consequent, ['⊥']], step_open_sups[:]])
                derivation3.extend(new_steps)

        elif derivation2[step][1] == "MT":
            # A MT step looks either like:
            # [ [¬, [p]], 'MT', [ [[p], then, [q]], [¬, [q]] ] ] or
            # [ [¬, [p]], 'MT', [ [[p], then, [¬ [q]]], [q] ] ]

            negated_antecedent = derivation2[step][0]
            antecedent = negated_antecedent[1]
            conditional = derivation2[step][2][0]
            consequent = conditional[2]
            independent_formula = derivation2[step][2][1]

            new_steps = list()
            step_open_sups.append(antecedent)
            new_steps.append([antecedent, 'SUP', [], step_open_sups[:]])
            new_steps.append([consequent, 'E→', [conditional, antecedent], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [consequent, independent_formula], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([negated_antecedent, 'I¬', [antecedent, ['⊥']], step_open_sups[:]])
            derivation3.extend(new_steps)

        elif derivation2[step][1] == "SD":
            # A SD step looks either like:
            # [ [p], 'SD', [ [[p], or, [q]], [¬, [q]] ] ]
            # [ [q], 'SD', [ [[p], or, [q]], [¬, [p]] ] ]
            # [ [p], 'SD', [ [[p], or, [¬, [q]]], [q] ] ]
            # [ [q], 'SD', [ [[¬, [p]], or, [q]], [p] ] ]

            disjunction = derivation2[step][2][0]
            derived_disjunct = derivation2[step][0]
            independent_formula = derivation2[step][2][1]

            new_steps = list()
            step_open_sups.append(['¬', derived_disjunct])
            new_steps.append([['¬', derived_disjunct], 'SUP', [], step_open_sups[:]])
            step_open_sups.append(disjunction[0])
            new_steps.append([disjunction[0], 'SUP', [], step_open_sups[:]])
            if len(disjunction[0]) == 2 and independent_formula == disjunction[0][1]:
                new_steps.append([['⊥'], 'E¬', [independent_formula, disjunction[0]], step_open_sups[:]])
            else:
                new_steps.append([['⊥'], 'E¬', [disjunction[0], ['¬', disjunction[0]]], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([[disjunction[0], '→', ['⊥']], 'I→', [disjunction[0], ['⊥']], step_open_sups[:]])
            step_open_sups.append(disjunction[2])
            new_steps.append([disjunction[2], 'SUP', [], step_open_sups[:]])
            if len(disjunction[2]) == 2 and independent_formula == disjunction[2][1]:
                new_steps.append([['⊥'], 'E¬', [independent_formula, disjunction[2]], step_open_sups[:]])
            else:
                new_steps.append([['⊥'], 'E¬', [disjunction[2], ['¬', disjunction[2]]], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([[disjunction[2], '→', ['⊥']], 'I→', [disjunction[2], ['⊥']], step_open_sups[:]])
            new_steps.append([['⊥'], 'E˅', [disjunction,
                                            [disjunction[0], '→', ['⊥']],
                                            [disjunction[2], '→', ['⊥']]], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([['¬', ['¬', derived_disjunct]], 'I¬',
                              [['¬', derived_disjunct], ['⊥']], step_open_sups[:]])
            new_steps.append([derived_disjunct, 'DN', [['¬', ['¬', derived_disjunct]]], step_open_sups[:]])
            derivation3.extend(new_steps)

        elif derivation2[step][1] == "NegUniv":
            # A NegUniv steps looks like [ [E, x, [¬,[Phi]] , NegUniv, [ [¬, [V, x, [Phi]]] ] ]
            negated_universal = derivation2[step][2][0]
            universal = negated_universal[1]
            existential = derivation[step][0]
            variable = universal[1]
            phi = universal[2]

            new_steps = list()
            step_open_sups.append(['¬', existential])
            new_steps.append([['¬', existential], 'SUP', [], step_open_sups[:]])
            subst = substitute(phi, variable, cts_unused[0], Classical2)
            del cts_unused[0]
            step_open_sups.append(['¬', subst])
            new_steps.append([['¬', subst], 'SUP', [], step_open_sups[:]])
            new_steps.append([existential, 'I∃', [['¬', subst]], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [['¬', existential], existential], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([['¬', ['¬', subst]], 'I¬', [['¬', subst], ['⊥']], step_open_sups[:]])
            new_steps.append([subst, 'DN', [['¬', ['¬', subst]]], step_open_sups[:]])
            new_steps.append([universal, 'I∀', [subst], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [negated_universal, universal], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([['¬', ['¬', existential]], 'I¬', [['¬', existential], ['⊥']], step_open_sups[:]])
            new_steps.append([existential, 'DN', [['¬', ['¬', existential]]], step_open_sups[:]])
            derivation3.extend(new_steps)

        elif derivation2[step][1] == "NegExist":
            # A NegExist steps looks like [ [V, x, [¬,[Phi]] , NegUniv, [ [¬, [E, x, [Phi]]] ] ]
            negated_existential = derivation2[step][2][0]
            existential = negated_existential[1]
            universal = derivation[step][0]
            variable = existential[1]
            phi = existential[2]

            new_steps = list()
            subst = substitute(phi, variable, cts_unused[0], Classical2)
            del cts_unused[0]
            step_open_sups.append(subst)
            new_steps.append([subst, 'SUP', [], step_open_sups[:]])
            new_steps.append([existential, 'I∃', [subst], step_open_sups[:]])
            new_steps.append([['⊥'], 'E¬', [negated_existential, existential], step_open_sups[:]])
            del step_open_sups[-1]
            new_steps.append([['¬', subst], 'I¬', [subst, ['⊥']], step_open_sups[:]])
            new_steps.append([universal, 'I∀', [['¬', subst]], step_open_sups[:]])
            derivation3.extend(new_steps)

        else:
            derivation3.append(derivation2[step])

    return derivation3


# ----------------------------------------------------------------------------------------------------------------------

preset_excercises = [
    '∀x Px / ∀y Py',
    '∃x Px / ∃y Py',
    '∀x ∀y Rxy, Pa / ∀x Rxx',
    '∃y Py, Rab / ∃x (Px ˅ Qx)',
    '∀x Px / ¬∃x ¬Px',
    '∃x Px / ¬∀x ¬Px',
    '∀x ¬Px / ¬∃x Px',
    '∃x ¬Px / ¬∀x Px',
    '¬∀x Px / ∃x ¬Px',
    '¬∃x Px / ∀x ¬Px',
    '∀x ∀y Rxy / ∀y ∀x Rxy',
    '∃x ∃y Rxy / ∃y ∃x Rxy',
    '∃x ∀y Rxy / ∀y ∃x Rxy',
    '∀x ¬Px / ∀y (Py → Ry)',
    '/ ∀x (Px ˅ ¬Px)',
    '∀x (Px → Qx), ∀x (Qx → Rx) / ∀x (Px → Rx)',
    '∀x Px ˄ ∀x Qx, ∀x (Px → Rx) / ∀x Rx',
    '∀x (Px → Qx), ∀x (¬Sx → ¬Qx) / ∀x (Px → (Sx ˅ Rx))',
    '∀x Rxa, ∃x Rxb / ∃x ∃y (Rxa ˄ Ryb)',
    '∀x (Ax ˄ ¬Bx) / ∀y ¬(Ay → By)',
    '∃x ¬(Px → Qx) / ¬∀x (Px → Qx)',
    '∀x ¬¬(Ax → Bx) / ¬∃x (Ax ˄ ¬Bx)',
    '∀x (Px → Qx), ∀x (Qx → ¬Rx) / ¬∃x ¬(Px → ¬Rx)',
    '¬∃x ¬(¬Px ˅ Sx), ∃x ¬Sx / ∃x ¬Px',
    '∀x (Rx → ¬Qx), ∀x (Px → Qx) / ∀x (¬Px ˅ ¬Rx)',
    '∀x Px → ∀x Qx, ¬Qa / ¬∀x Px',
    '∀x (Px → Qx), ∀x (¬Sx → ¬Qx), ∀x ¬Sx / ∃x ¬Px',
    '∀x (Tx → Qx), ∀x ¬(Px ˅ ¬Tx) / ∃x (¬Px ˄ Qx)',
    '∀x (Sx → ¬Rx), ∃x ¬(¬Px ˅ ¬Rx) / ∃x (Px ˄ ¬Sx)',
    '∀x (Px → (Qx ˅ Rx)), ∃x (¬Qx ˄ Px) / ∃x Rx'
]
