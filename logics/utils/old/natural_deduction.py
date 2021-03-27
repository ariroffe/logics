try:
    from utils_formula_parser import atomics
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import atomics


# Format for a derivation is:
# deriv = {1: {'formula': [formula], 'rule': rule_func, 'on_steps': {steps}, 'open_sups': [open_sups]}
#          2: ...

# For suppositions, rule is 'SUP', steps is set()
# For premises, rule is 'PREM', steps is set()


def check_derivation(derivation, premises, conclusion):
    """Checks if a derivation is ok. If it is, returns an empty list, otherwise returns [step, error]
       Does not check if the conclusion and premises are ok, for that there is another function"""
    for step in sorted(derivation):
        try:
            # See that the on steps are all between 1 and the current step
            for s in derivation[step]['on_steps']:
                if not 0 < s < step:
                    raise ValueError("Incorrect 'on steps' specification")
            current_sups = derivation[step]['open_sups'][:]
            previous_sups = list()
            if step > 1:
                previous_sups = derivation[step-1]['open_sups'][:]

            # If the step does not open or close any previous supossitions, or closes the last open one
            if (current_sups == previous_sups or current_sups == previous_sups[:-1]) and \
                    derivation[step]['rule'] != 'SUP':

                if derivation[step]['rule'] == 'PREM':
                    # Check that the formula is a premise
                    if derivation[step]['formula'] not in premises:
                        raise ValueError("Formula given is not among the premises")
                    # Check that this is the first step or that the previous step is also a premise
                    # And that the steps field is empty
                    if (step == 1 or derivation[step-1]['rule'] == 'PREM') and derivation[step]['on_steps'] == list():
                        pass
                    else:
                        raise ValueError("Premises go at the beggining of the derivation and have empty 'on steps'")
                else:
                    # A rule is being applied
                    prev_steps = list()
                    for s in derivation[step]['on_steps']:
                        if s not in derivation:
                            raise ValueError(f"Non existent step {s}")
                        prev_steps.append(derivation[s])

                    results = derivation[step]['rule'](derivation[step], prev_steps)
                    is_ok = False
                    for result in results:
                        if derivation[step]['formula'] == result:
                            is_ok = True
                    if not is_ok:
                        raise ValueError("Rule incorrectly applied")
                    # Y FINALMENTE VER SI LA FORMULA DEL PASO COINCIDE CON ALGUNO DE LOS RETURNS
                    pass

            # If it contains one more supposition (the current step opens one)
            elif current_sups[:-1] == previous_sups and current_sups[-1] == step:
                # The rule must be SUP and the on_steps must be empty
                if derivation[step]['rule'] == 'SUP' and derivation[step]['on_steps'] == list():
                    pass
                else:
                    raise ValueError("Only SUP can open suppositions, and it must have empty 'on steps'")

            else:
                raise ValueError("Incorrect handling of suppositions")

        except ValueError as e:
            return [step, str(e)]

    # Lastly, see that the derivation does not contain open suppositions at the last step,
    # and that the conclusion is the last step
    last_step = max(derivation)
    if derivation[last_step]['open_sups'] != list():
        return [last_step, 'The derivation ends with open suppositions']
    elif derivation[last_step]['formula'] != conclusion:
        return [last_step, 'The rules are correctly applied but the final formula is not the conclusion']

    return []


# ----------------------------------------------------------------------------------------------------------------------
# DERIVATION SOLVER
# Uses a different format than check_derivation (derivations are lists of lists, not dicts of dicts)


def solve_derivation(premises, conclusion):

    derivation = [[x[:], 'PREM', []] for x in premises]
    goal = conclusion

    while True:
        # Apply simplification rules (elimination + a couple more)
        derivation = apply_simplification_rules(derivation, goal)

        # The goal has been reached
        if goal in [x[0] for x in derivation]:
            if derivation[-1][0] != goal:
                derivation.append([goal, 'REP', [goal]])
            return derivation

        # If Falsum is in the derivation apply EFSQ
        elif ['⊥'] in [x[0] for x in derivation]:
            derivation.append([goal, 'EFSQ', [['⊥']]])
            return derivation

        # If the goal is Falsum, and the simplification rules did not provide it, raise an error
        elif goal == ['⊥']:
            raise ValueError("Goal is ⊥ and elimination rules did not resolve the derivation")

        # If the goal is an atomic, try reductio
        elif len(goal) == 1 and goal[0] in atomics:
            prems = [x[0] for x in derivation]
            prems.append(['¬', goal])
            deriv = solve_derivation(prems, ['⊥'])

            derivation.append([['¬', goal], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
            derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
            return derivation

        # If the goal is a negation, try reductio
        elif len(goal) == 2 and goal[0] == '¬':
            prems = [x[0] for x in derivation]
            prems.append(goal[1])
            deriv = solve_derivation(prems, ['⊥'])

            derivation.append([goal[1], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([goal, "I¬", [goal[1], ['⊥']]])
            return derivation

        # If the goal is a conjunction, make two derivations of both conjuncts
        elif len(goal) == 3 and goal[1] == '˄':
            prems = [x[0] for x in derivation]
            deriv1 = solve_derivation(prems, goal[0])
            deriv2 = solve_derivation(prems, goal[2])

            derivation.extend([x for x in deriv1 if x[1] != 'PREM'])
            derivation.extend([x for x in deriv2 if x[1] != 'PREM'])
            derivation.append([goal, "I˄", [goal[0], goal[2]]])

            return derivation

        # If the goal is a conditional, take the antecedent as premise and set as goal the conclusion
        elif len(goal) == 3 and goal[1] == '→':
            prems = [x[0] for x in derivation]
            prems.append(goal[0])
            deriv = solve_derivation(prems, goal[2])

            derivation.append([goal[0], 'SUP', []])
            derivation.extend([x for x in deriv if x[1] != 'PREM'])
            derivation.append([goal, "I→", [goal[0], goal[2]]])
            return derivation

        # If the goal is a disjunction, try to derive each disjunct separately
        # If that fails, try reductio
        elif len(goal) == 3 and goal[1] == '˅':
            prems = [x[0] for x in derivation]
            try:
                deriv = solve_derivation(prems, goal[0])
                derivation.extend([x for x in deriv if x[1] != 'PREM'])
                derivation.append([goal, 'I˅', [goal[0]]])
                return derivation
            except ValueError:
                try:
                    deriv = solve_derivation(prems, goal[2])
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([goal, 'I˅', [goal[2]]])
                    return derivation
                except ValueError:

                    prems.append(['¬', goal])
                    deriv = solve_derivation(prems, ['⊥'])

                    derivation.append([['¬', goal], 'SUP', []])
                    derivation.extend([x for x in deriv if x[1] != 'PREM'])
                    derivation.append([['¬', ['¬', goal]], "I¬", [['¬', goal], ['⊥']]])
                    derivation.append([goal, "DN", [['¬', ['¬', goal]]]])
                    return derivation
        else:
            raise ValueError(str(goal))


def apply_simplification_rules(derivation, goal):
    """Makes changes and records the indexes on applied_rules (so that it doesn't repeat them)
    When it has no more changes to make (modif = False), returns"""

    applied_rules = {'E˄': [], 'E→': [], 'MT': [], 'E˅': [], 'DN': [],
                     'DM': [], 'DM2': [], 'NegCond': [], 'E¬': [], 'SD': []}
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

    # First, replace the derived rules with their hardcoded demonstration
    derivation = replace_derived_rules(derivation)

    # Second, add the open_sups as a fourth list in each step
    derivation = add_open_sups(derivation)

    # Third, delete the steps that are never used
    used_steps = register_steps(derivation, derivation[-1], len(derivation)-1, [len(derivation)-1])
    prem_steps = [x for x in derivation if x[1] == 'PREM']
    prem_indexes = [derivation.index(x) for x in prem_steps]
    used_steps.extend(prem_indexes)
    used_steps = list(set(used_steps))  # Remove repetitions from used_steps
    used_steps.sort()                   # Order them
    derivation = [derivation[index] for index in used_steps]

    # Lastly, replace the on_steps with numbers and add necessary REP steps
    derivation = numerate_on_steps(derivation)

    return derivation


def add_open_sups(derivation):
    """Adds the open sups line as a fourth element (index3)"""
    open_sups = list()
    for step in range(len(derivation)):
        if derivation[step][1] == 'SUP':
            open_sups.append(derivation[step][0])
        elif derivation[step][1] == 'I¬' or derivation[step][1] == 'I→':
            del open_sups[-1]
        derivation[step].append(open_sups[:])
    return derivation


def register_steps(derivation, step, current_index, used_steps):
    """Return a list of the indexes of the used steps in the derivation"""

    # If no previous step was used in step (PREM or SUP), returns the input
    if step[2] == list():
        return used_steps

    # If previous steps is not empty
    else:
        # If the rule does not close a supposition
        if step[1] != 'I→' and step[1] != 'I¬':
            for formula in step[2]:
                # Look for the last aparition of the formula that is at the same level of supposition or above
                formula_step = None
                for step2 in range(current_index):
                    if derivation[step2][0] == formula:
                        # See that step2 has no open suppositions that are not open in step
                        inapplicable = False
                        for x in derivation[step2][3]:
                            if x not in step[3] or len(derivation[step2][3]) > len(step[3]):
                                inapplicable = True
                        if not inapplicable:
                            formula_step = step2
                used_steps.append(formula_step)
                used_steps = register_steps(derivation, derivation[formula_step], formula_step, used_steps)
            return used_steps

        # If the rule does close a supposition
        else:
            # The last formula is used
            used_steps.append(current_index - 1)
            used_steps = register_steps(derivation, derivation[current_index-1], current_index-1, used_steps)

            # We have the open sups in the index 3 of the step. Register the sup level at the step before
            last_sup_level = derivation[current_index - 1][3]
            # Now go back to a point where there is one less open sup
            for step2 in range(current_index-1, -1, -1):
                if len(derivation[step2][3]) < len(last_sup_level):
                    used_steps.append(step2 + 1)
                    used_steps = register_steps(derivation, derivation[step2 + 1], current_index - 1, used_steps)
                    return used_steps
            # If the derivation begins with a sup there is no level with less supossitions
            # So it has not entered the if above. Register the first step then
            used_steps.append(0)
            used_steps = register_steps(derivation, derivation[0], 0, used_steps)
            return used_steps


def replace_derived_rules(derivation):
    """Replaces DM, DM2, NegCond, MT, SD with their hardcoded derivation"""

    derivation2 = list()

    # In the first pass it replaces only DM2 (since DM2 uses DM)
    for step in range(len(derivation)):
        if derivation[step][1] == "DM2":
            # A DM2 step has structure [ [[¬, [p]], or, [¬, [q]]], 'DM2', [[¬, [[p], & [q]]]] ]
            negated_conjunction = derivation[step][2][0]
            disjunction = derivation[step][0]

            new_steps = list()
            new_steps.append([['¬', disjunction], 'SUP', []])
            new_steps.append([['¬', disjunction[0]], 'DM', [['¬', disjunction]]])
            new_steps.append([['¬', disjunction[2]], 'DM', [['¬', disjunction]]])
            new_steps.append([disjunction[0][1], 'DN', [['¬', disjunction[0]]]])
            new_steps.append([disjunction[2][1], 'DN', [['¬', disjunction[2]]]])
            new_steps.append([negated_conjunction[1], 'I˄',[disjunction[0][1], disjunction[2][1]]])
            new_steps.append([['⊥'], 'E¬', [negated_conjunction, negated_conjunction[1]]])
            new_steps.append([['¬', ['¬', disjunction]], 'I¬', [['¬', disjunction], ['⊥']]])
            new_steps.append([disjunction, 'DN', [['¬', ['¬', disjunction]]]])
            derivation2.extend(new_steps)

        else: derivation2.append(derivation[step])

    derivation3 = list()

    # Second pass: The rest of the rules
    for step in range(len(derivation2)):
        if derivation2[step][1] == "DM":
            # A DM steps looks like [ [¬,[p]], DM, [[¬,[[p] v [q]]]] ] or like [ [¬,[q]], DM, [[¬,[[p] v [q]]]] ]
            negated_disjunct = derivation2[step][0]
            disjunct = negated_disjunct[1]
            negated_disjunction = derivation2[step][2][0]
            disjunction = negated_disjunction[1]

            new_steps = list()
            new_steps.append([disjunct, 'SUP', []])
            new_steps.append([disjunction, 'I˅', [disjunct]])
            new_steps.append([['⊥'], 'E¬', [negated_disjunction, disjunction]])
            new_steps.append([negated_disjunct, 'I¬', [disjunct, ['⊥']]])
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
                new_steps.append([['¬', antecedent], 'SUP', []])
                new_steps.append([antecedent, 'SUP', []])
                new_steps.append([['⊥'], 'E¬', [['¬', antecedent], antecedent]])
                new_steps.append([consequent, 'EFSQ', [['⊥']]])
                new_steps.append([conditional, 'I→', [antecedent, consequent]])
                new_steps.append([['⊥'], 'E¬', [negated_conditional, conditional]])
                new_steps.append([['¬', ['¬', antecedent]], 'I¬', [['¬', antecedent], ['⊥']]])
                new_steps.append([antecedent, 'DN', [['¬', ['¬', antecedent]]]])
                derivation3.extend(new_steps)

            elif derivation2[step][0] == ['¬', consequent]:
                new_steps = list()
                new_steps.append([consequent, 'SUP', []])
                new_steps.append([antecedent, 'SUP', []])
                new_steps.append([consequent, 'REP', [consequent]])
                new_steps.append([conditional, 'I→', [consequent, antecedent]])
                new_steps.append([['⊥'], 'E¬', [conditional, negated_conditional]])
                new_steps.append([['¬', consequent], 'I¬', [consequent, ['⊥']]])
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
            new_steps.append([antecedent, 'SUP', []])
            new_steps.append([consequent, 'E→', [conditional, antecedent]])
            new_steps.append([['⊥'], 'E¬', [consequent, independent_formula]])
            new_steps.append([negated_antecedent, 'I¬', [antecedent, ['⊥']]])
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
            new_steps.append([['¬', derived_disjunct], 'SUP', []])
            new_steps.append([disjunction[0], 'SUP', []])
            if len(disjunction[0]) == 2 and independent_formula == disjunction[0][1]:
                new_steps.append([['⊥'], 'E¬', [independent_formula, disjunction[0]]])
            else:
                new_steps.append([['⊥'], 'E¬', [disjunction[0], ['¬', disjunction[0]]]])
            new_steps.append([[disjunction[0], '→', ['⊥']], 'I→', [disjunction[0], ['⊥']]])
            new_steps.append([disjunction[2], 'SUP', []])
            if len(disjunction[2]) == 2 and independent_formula == disjunction[2][1]:
                new_steps.append([['⊥'], 'E¬', [independent_formula, disjunction[2]]])
            else:
                new_steps.append([['⊥'], 'E¬', [disjunction[2], ['¬', disjunction[2]]]])
            new_steps.append([[disjunction[2], '→', ['⊥']], 'I→', [disjunction[2], ['⊥']]])
            new_steps.append([['⊥'], 'E˅', [disjunction,
                                                    [disjunction[0], '→', ['⊥']],
                                                    [disjunction[2], '→', ['⊥']]]])
            new_steps.append([['¬',['¬', derived_disjunct]], 'I¬', [['¬', derived_disjunct], ['⊥']]])
            new_steps.append([derived_disjunct, 'DN', [['¬',['¬', derived_disjunct]]]])
            derivation3.extend(new_steps)

        else:
            derivation3.append(derivation2[step])

    return derivation3


def numerate_on_steps(derivation):
    """Replaces the third column (index 2) with numbers
    and adds the necessary rep steps (when a steps says eg 1, 1 on its on_steps)"""

    steps_to_insert = list()

    for step in range(len(derivation)):

        # SUP or PREM does not do anything
        if derivation[step][2] == list():
            derivation[step][2] = ''
        else:
            # Rules that do not close suppositions
            if derivation[step][1] != 'I→' and derivation[step][1] != 'I¬':
                new_steps = list()
                for formula in derivation[step][2]:
                    # Look for the last aparition of the formula that is at the same level of supposition or above
                    formula_step = None
                    for step2 in range(step):
                        if derivation[step2][0] == formula:
                            # See that step2 has no open suppositions that are not open in step
                            inapplicable = False
                            for x in derivation[step2][3]:
                                if x not in derivation[step][3] or len(derivation[step2][3]) > len(derivation[step][3]):
                                    inapplicable = True
                            if not inapplicable:
                                formula_step = step2 + 1
                    new_steps.append(formula_step)
                # If the new_steps are the same (ej I&, 1, 1) then put a repetition at the same rep level
                for s1 in new_steps:
                    if new_steps.count(s1) > 1:
                        steps_to_insert.append([step, [derivation[s1-1][0], 'REP', s1, derivation[step][3]]])
                        break
                derivation[step][2] = str(sorted(new_steps))[1:-1]

            # Rules that close suppositions
            else:
                # The last formula is used
                new_steps = [step]  # (remember that step already has -1 bc the range goes from 0)

                # We have the open sups in the index 3 of the step. Register the sup level at the step before
                last_sup_level = derivation[step - 1][3]
                last_sup_number = -1
                # Now go back to a point where there is one less open sup
                for step2 in range(step - 1, -1, -1):
                    if len(derivation[step2][3]) < len(last_sup_level):
                        last_sup_number = step2 + 2
                        break
                # If the derivation begins with a sup there is no level with less supossitions
                if last_sup_number == -1:
                    last_sup_number = 1
                new_steps.insert(0, last_sup_number)
                for s1 in new_steps:
                    if new_steps.count(s1) > 1:
                        steps_to_insert.append([step, [derivation[s1-1][0], 'REP', s1, derivation[step-1][3]]])
                        break
                derivation[step][2] = str(new_steps)[1:-1].replace(",", "-").replace(" ", "")

    # Add the necessary repetition steps
    sum_to_rep = 0
    for ins in steps_to_insert:
        at_index = ins[0] + sum_to_rep
        at_step = at_index + 1

        ins[1][2] = ins[1][2] + sum_to_rep    # This and the next line are for when it is putting more than one rep
        sum_to_rep += 1

        line = ins[1]
        derivation2 = derivation[:at_index]
        derivation2.append(line)
        derivation2.extend(derivation[at_index:])
        derivation = derivation2[:]

        # Modify the next line
        next_on_steps = derivation[at_index+1][2]
        next_on_steps = next_on_steps.replace(" ", "")
        slash = False
        if "-" in next_on_steps:
            next_on_steps = next_on_steps.replace("-", ",")
            slash = True
        next_on_steps = next_on_steps.split(",")
        for x in range(len(next_on_steps)-1, -1, -1):
            if next_on_steps.count(next_on_steps[x]) > 1:
                next_on_steps[x] = str(int(next_on_steps[x]) + 1)
                break
        next_on_steps = str(next_on_steps).replace("'","")[1:-1]
        if slash:
            next_on_steps = next_on_steps.replace(", ", "-")
        derivation[at_index+1][2] = next_on_steps

        # Now we have to sum 1 to every on_step equal or greater than at_step
        for step in range(at_index+2, len(derivation)):
            at_steps_string = derivation[step][2]
            if at_steps_string:
                at_steps_string.replace(" ", "")
                slash = False
                if "-" in at_steps_string:
                    at_steps_string = at_steps_string.replace("-", ",")
                    slash = True
                at_steps_list = at_steps_string.split(",")
                at_steps_list = [str(int(x)+1) if int(x) >= at_step else x for x in at_steps_list]
                new_string = str(at_steps_list).replace("'", "")[1:-1]
                if slash:
                    new_string = new_string.replace(", ", "-")
                derivation[step][2] = new_string

    return derivation
