"""
DERIVATION SOLVER
This is a homemade heuristic solver for classical natural deduction as presented in GAMUT.
It is not complete, meaning, there are valid inferences it does not prove.
It could be better to have logics interface with some known ATP to do this
"""
from copy import copy

from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories import Derivation, NaturalDeductionStep
from logics.classes.exceptions import SolverError


class ClassicalNaturalDeductionSolver:
    def solve(self, inference):
        """This is the function you should always call from this class"""
        derivation = self.solve_derivation(inference)   # Actually solves the derivation (using some derived rules)
        derivation = self.clean_derivation(derivation, inference)  # Deletes unnecesary steps and replaces derived rules
        return derivation

    # ------------------------------------------------------------------------------------------------------------------

    def solve_derivation(self, inference, open_sups=None, jump_steps=None):
        """
        First of the two algorithms of the solver, basically analizes the goal and sets a new goal

        open_sups and jump_steps should be left as the default values
        The first is so that recursive iterations preserve suppositions from the above ones
        The second is because of how conjunction introduction works (makes two derivations separately, so the step
        numbers in the second should jump over some values) - e.g. in p, q, r / (q → p) ∧ (r → p) the derivation of
        (r → p) should start the supposition not in step 3, but after the last step of the derivation of (q → p).
        When it is not None, will come in format [[3, 4], [7, 3]], meaning:
            - for a step greater or equal than 3 you sould add 4 steps
            - for a step greater or equal than 7, add 3 more steps
        In the case above, jump_steps will include [3, 2] in the recursive iteration to solve the second conjunct -
        all it will be able to "see" are the premises (not the conditional introduction for the first conjunct) -
        thus, step 3 it will suppose q, step 4 repeat p and the next supposition (of r) should be in step 5, not 3
        """
        # Open sups will be None only in the first recursive call
        if open_sups is None:
            open_sups = []

        goal = inference.conclusion
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise',
                                                      open_suppositions=copy(open_sups)) for p in inference.premises])

        for prem_number in range(len(derivation)):
            # The goal is already present as premise, return the derivation with the premise repeated
            if derivation[prem_number].content == goal:
                return derivation
            # You have ⊥ as a premise, apply EFSQ
            elif derivation[prem_number].content == Formula(['⊥']):
                if derivation[-1].content != goal:
                    derivation.append(NaturalDeductionStep(content=goal, justification='EFSQ',
                                                           on_steps=self.steps([prem_number], jump_steps),
                                                           open_suppositions=copy(open_sups)))
                return derivation

        # Apply simplification rules (elimination + a couple more, see below)
        derivation = self.apply_simplification_rules(derivation, goal, jump_steps=jump_steps)

        # The goal has been reached by the application of the rules (the second algorithm exits if it finds the goal)
        if derivation and derivation[-1].content == goal:
            return derivation
        # The second algorithm also exits if it derives ⊥. If you did (and ⊥ was not your goal), simply apply EFSQ
        elif derivation and derivation[-1].content == Formula(['⊥']):
            derivation.append(NaturalDeductionStep(content=goal, justification='EFSQ',
                                                   on_steps=self.steps([len(derivation)-1], jump_steps),
                                                   open_suppositions=copy(open_sups)))
            return derivation

        # If the goal is a conjunction, make two derivations, one for each conjunct
        if goal[0] == '∧':
            try:
                derivation_formulae = [step.content for step in derivation]
                prems = copy(derivation_formulae)

                # Solve the derivation of the first conjunct
                deriv1 = self.solve_derivation(inference=Inference(prems, [goal[1]]),
                                               open_sups=copy(open_sups), jump_steps=jump_steps)

                # Save the step where the first conjunct is, for the introduction later
                # (the step may not be the last of deriv1 if the first conjunct was already present as premise)
                first_conjunct_step = next(index for index in range(len(deriv1)) if
                                           deriv1[index].content == goal[1] and
                                           deriv1[index].open_suppositions <= open_sups)
                first_conjunct_step = self.steps([first_conjunct_step], jump_steps)[0]

                # If asked for a conjunction between the same two formulas, simply repeat the first conjunct
                # (more efficient, and otherwise p / p ∧ p would have on steps [1, 1] which is wrong)
                if goal[1] == goal[2]:
                    derivation.extend([step for step in deriv1 if step.justification != 'premise'])
                    derivation.append(NaturalDeductionStep(content=goal[2], justification="repetition",
                                                           on_steps=[first_conjunct_step],
                                                           open_suppositions=copy(open_sups)))
                    derivation.append(NaturalDeductionStep(content=goal, justification="I∧",
                                                           on_steps=[first_conjunct_step,
                                                                     self.steps([len(derivation)-1], jump_steps)[0]],
                                                           open_suppositions=copy(open_sups)))
                    return derivation

                # Otherwise, if the second conjunct is different
                if jump_steps is None:
                    jump_steps = [[len(derivation_formulae), len(deriv1) - len(derivation_formulae)]]
                    # e.g. if the base derivation has 2 steps and deriv1 has 5, jump_steps will be [2, 3]
                    # meaning: for a step equal or greater than 2, add 3 steps (step 2 becomes step 5)
                else:
                    jump_steps = copy(jump_steps)  # To not alter previous recursive iterations
                    jump_steps.append([len(derivation_formulae), len(deriv1) - len(derivation_formulae)])

                # Solve the derivation for the second conjunct
                # deriv 2 does not see deriv1, so it cannot use anything in a closed supposition within it
                deriv2 = self.solve_derivation(inference=Inference(prems, [goal[2]]),
                                               open_sups=copy(open_sups), jump_steps=jump_steps)

                # Save the step where the second conjunct is, for the introduction later
                second_conjunct_step = next(index for index in range(len(deriv2)) if
                                            deriv2[index].content == goal[2] and
                                            deriv2[index].open_suppositions <= open_sups)
                second_conjunct_step = self.steps([second_conjunct_step], jump_steps)[0]

                # AFTER fixing the step numbers (important), extend derivation
                derivation.extend([step for step in deriv1 if step.justification != 'premise'])
                derivation.extend([step for step in deriv2 if step.justification != 'premise'])

                derivation.append(NaturalDeductionStep(content=goal, justification="I∧",
                                                       on_steps=[first_conjunct_step, second_conjunct_step],
                                                       open_suppositions=copy(open_sups)))
                return derivation

            except SolverError:
                pass

        # If the goal is a conditional, take the antecedent as premise and set the consequent as goal
        elif goal[0] == '→':
            try:
                # Add the antecedent as a supposition
                sup_intro_number = self.steps([len(derivation)], jump_steps)[0]
                # Copy the open_sups and the derivation in case supposing the antecedent fails and we need
                # to try reductio
                open_sups2 = open_sups + [sup_intro_number]
                derivation2 = copy(derivation)
                derivation2.append(NaturalDeductionStep(content=goal[1], justification='supposition',
                                                       on_steps=[], open_suppositions=copy(open_sups2)))
                prems = [step.content for step in derivation2]  # not derivation_formulae bc missing the antecedent

                deriv = self.solve_derivation(inference=Inference(prems, [goal[2]]),
                                              open_sups=copy(open_sups2), jump_steps=jump_steps)

                # If deriv and derivation have the same number of steps, it is because the derivation already contained
                # the consequent, and therefore it just returned. We need to repeat the consequent to close it.
                if len(deriv) == len(derivation2):
                    consequent_step = next(index for index in range(len(derivation2)) if
                                           derivation2[index].content == goal[2])
                    consequent_step = self.steps([consequent_step], jump_steps)
                    deriv.append(NaturalDeductionStep(content=goal[2], justification='repetition',
                                                      on_steps=consequent_step,
                                                      open_suppositions=copy(open_sups2)))

                derivation2.extend([x for x in deriv if x.justification != 'premise'])
                derivation2.append(NaturalDeductionStep(content=goal, justification="I→",
                                                       on_steps=[sup_intro_number,  # first number has jump calculated
                                                                 self.steps([len(derivation2)-1], jump_steps)[0]],
                                                       open_suppositions=open_sups2[:-1]))
                return derivation2

            except SolverError:
                pass

        # If the goal is a disjunction, try to derive each disjunct separately
        elif goal[0] == '∨':
            derivation_formulae = [step.content for step in derivation]
            prems = copy(derivation_formulae)
            for disjunct in (1, 2):
                try:
                    deriv = self.solve_derivation(inference=Inference(prems, [goal[disjunct]]),
                                                  open_sups=copy(open_sups), jump_steps=jump_steps)
                    derivation.extend([x for x in deriv if x.justification != 'premise'])

                    # Look for where the disjunct is (may not be the last step if it was present as premise)
                    step_num = next(index for index in range(len(derivation)) if
                                    derivation[index].content == goal[disjunct] and
                                    derivation[index].open_suppositions <= open_sups)
                    step_num = self.steps([step_num], jump_steps)  # this returns a list
                    derivation.append(NaturalDeductionStep(content=goal, justification='I∨',
                                                           on_steps=step_num,
                                                           open_suppositions=copy(open_sups)))

                    return derivation

                except SolverError:
                    pass

        # If the above fails or does not apply (e.g. the goal is an atomic or a negated formula), try reductio
        if goal != Formula(['⊥']):
            sup_intro_number = self.steps([len(derivation)], jump_steps)[0]
            open_sups2 = open_sups + [sup_intro_number]
            derivation.append(NaturalDeductionStep(content=Formula(['~', goal]), justification='supposition',
                                                   open_suppositions=copy(open_sups2)))

            derivation_formulae = [step.content for step in derivation]
            prems = copy(derivation_formulae)
            inf = Inference(premises=prems, conclusions=[Formula(['⊥'])])

            deriv = self.solve_derivation(inference=inf, open_sups=copy(open_sups2), jump_steps=jump_steps)

            derivation.extend([x for x in deriv if x.justification != 'premise'])
            derivation.append(NaturalDeductionStep(content=Formula(['~', ['~', goal]]),
                                                   justification="I~",
                                                   on_steps=[sup_intro_number,  # first number has jump calculated
                                                             self.steps([len(derivation) - 1], jump_steps)[0]],
                                                   open_suppositions=open_sups2[:-1]))
            # No need to see if the goal was already in the derivation and therefore if it is not the last step, since
            # if ⊥ was present as premise, then the conclusion would have been reached by EFSQ, and we wouldn't have
            # entered this clause

            derivation.append(NaturalDeductionStep(content=goal, justification="~~",
                                                   on_steps=self.steps([len(derivation) - 1], jump_steps),
                                                   open_suppositions=open_sups2[:-1]))
            return derivation

        # If you did not return thus far (goal should be ⊥), raise an exception
        else:
            raise SolverError('Could not solve the derivation provided')

    # ------------------------------------------------------------------------------------------------------------------

    def apply_simplification_rules(self, derivation, goal, jump_steps=None):
        """
        Blindly derives everything it can but using only rules that simplify formulae, some of them derived
        (not things like I∨, which would be impossible to apply blindly)
        Makes changes and records the indexes on applied_rules (so that it doesn't repeat them)
        When it has no more changes to make (modif = False), returns
        """

        applied_rules = {'E∧': [], 'E→': [], 'MT': [], 'E∨': [], '~~': [],
                         'DM': [], 'DM2': [], 'NegCond': [], 'E~': [], 'SD': []}
        modif = True  # To track if changes were made. Will only exit when no changes occur in the whole next loop
        while modif:
            modif = False
            formulas_list = [x.content for x in derivation]
            formulas_list2 = formulas_list[:]
            if derivation:
                open_sups = derivation[-1].open_suppositions  # None of the following rules opens or closes suppositions
                # So open_suppositions will be copied from the last step in the original derivation
            else:
                open_sups = list()
            for formula in formulas_list:
                # Conjunction elimination
                if len(formula) == 3 and formula[0] == '∧':
                    if formulas_list.index(formula) not in applied_rules['E∧']:
                        if formula[1] not in formulas_list2:
                            formulas_list2.append(formula[1])
                            derivation.append(NaturalDeductionStep(content=formula[1], justification="E∧",
                                                                   on_steps=self.steps([formulas_list.index(formula)],
                                                                                       jump_steps),
                                                                   open_suppositions=copy(open_sups)))
                            if goal == formula[1]:
                                return derivation
                        if formula[2] not in formulas_list2:
                            formulas_list2.append(formula[2])
                            derivation.append(NaturalDeductionStep(content=formula[2], justification="E∧",
                                                                   on_steps=self.steps([formulas_list.index(formula)],
                                                                                       jump_steps),
                                                                   open_suppositions=copy(open_sups)))
                            if goal == formula[2]:
                                return derivation
                        applied_rules['E∧'].append(formulas_list.index(formula))
                        modif = True

                # Conditional elimination and modus tollens
                elif len(formula) == 3 and formula[0] == '→':
                    for formula2 in formulas_list:
                        # If the second formula is the antecent of the first, apply conditional elimination
                        if formula[1] == formula2:
                            if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['E→']:
                                if formula[2] not in formulas_list2:
                                    formulas_list2.append(formula[2])
                                    derivation.append(NaturalDeductionStep(content=formula[2], justification="E→",
                                                                           on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2)],
                                                                                        jump_steps),
                                                                           open_suppositions=copy(open_sups)))
                                    if goal == formula[2]:
                                        return derivation
                                applied_rules['E→'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                                modif = True
                        # Independent formula might be the negation of the consequent OR VICE VERSA (p then ~q, q / ~p)
                        # In that case, apply Modus Tollens
                        elif formula2 == Formula(['~', formula[2]]) or formula[2] == Formula(['~', formula2]):
                            if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['MT']:
                                if Formula(['~', formula[1]]) not in formulas_list2:
                                    formulas_list2.append(Formula(['~', formula[1]]))
                                    derivation.append(NaturalDeductionStep(content=Formula(['~', formula[1]]),
                                                                           justification="MT",
                                                                           on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2)],
                                                                                        jump_steps),
                                                                           open_suppositions=copy(open_sups)))
                                    if goal == Formula(['~', formula[1]]):
                                        return derivation
                                applied_rules['MT'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                                modif = True

                # Disjunction elimination and disjunctive syllogism
                elif len(formula) == 3 and formula[0] == '∨':
                    # See if it can find the first conditional
                    for formula2 in formulas_list:
                        if len(formula2) == 3 and formula2[0] == '→' and formula2[1] == formula[1]:
                            # It found a conditional formula with the left disjunct as antecedent
                            consequent = formula2[2]
                            # Try and find the second conditional (right disjunct --> consequent)
                            for formula3 in formulas_list[formulas_list.index(formula2) + 1:]:  # Look forward only
                                if len(formula3) == 3 and formula3[0] == '→' and \
                                        formula3[1] == formula[2] and formula3[2] == consequent:
                                    if (formulas_list.index(formula), formulas_list.index(formula2),
                                            formulas_list.index(formula3)) not in applied_rules['E∨']:
                                        if consequent not in formulas_list2:
                                            formulas_list2.append(consequent)
                                            derivation.append(NaturalDeductionStep(content=consequent,
                                                                                   justification="E∨",
                                                                                   on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2),
                                                                                        formulas_list.index(formula3)],
                                                                                        jump_steps),
                                                                                   open_suppositions=copy(open_sups)))
                                            if goal == consequent:
                                                return derivation
                                        applied_rules['E∨'].append((formulas_list.index(formula),
                                                                    formulas_list.index(formula2),
                                                                    formulas_list.index(formula3)))
                                        modif = True
                        # Disjunctive syllogism - Formula2 is the negation of the first disjunct
                        if formula[1] == Formula(['~', formula2]) or Formula(['~', formula[1]]) == formula2:
                            if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['SD']:
                                if formula[2] not in formulas_list2:
                                    formulas_list2.append(formula[2])
                                    derivation.append(NaturalDeductionStep(content=formula[2],
                                                                           justification="SD",
                                                                           on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2)],
                                                                                        jump_steps),
                                                                           open_suppositions=copy(open_sups)))
                                    if goal == formula[2]:
                                        return derivation
                                applied_rules['SD'].append((formulas_list.index(formula),
                                                            formulas_list.index(formula2)))
                                modif = True
                        # SD - Formula2 is the negation of the second disjunct
                        if formula[2] == ['~', formula2] or ['~', formula[2]] == formula2:
                            if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['SD']:
                                if formula[1] not in formulas_list2:
                                    formulas_list2.append(formula[1])
                                    derivation.append(NaturalDeductionStep(content=formula[1],
                                                                           justification="SD",
                                                                           on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2)],
                                                                                        jump_steps),
                                                                           open_suppositions=copy(open_sups)))
                                    if goal == formula[1]:
                                        return derivation
                                applied_rules['SD'].append((formulas_list.index(formula),
                                                            formulas_list.index(formula2)))
                                modif = True

                # The formula is a negation
                elif len(formula) == 2 and formula[0] == '~':
                    negated_formula = formula[1]
                    # If negating a negation, apply double negation
                    if len(negated_formula) == 2 and negated_formula[0] == '~':
                        if formulas_list.index(formula) not in applied_rules['~~']:
                            if negated_formula[1] not in formulas_list2:
                                formulas_list2.append(negated_formula[1])
                                derivation.append(NaturalDeductionStep(content=negated_formula[1],
                                                                       justification="~~",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == negated_formula[1]:
                                    return derivation
                            applied_rules['~~'].append(formulas_list.index(formula))
                            modif = True
                    # If negating a disjunction, apply DeMorgan
                    if len(negated_formula) == 3 and negated_formula[0] == '∨':
                        if formulas_list.index(formula) not in applied_rules['DM']:
                            # Add both separately instead of the conjunction
                            if Formula(['~', negated_formula[1]]) not in formulas_list2:
                                formulas_list2.append(Formula(['~', negated_formula[1]]))
                                derivation.append(NaturalDeductionStep(content=Formula(['~', negated_formula[1]]),
                                                                       justification="DM",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == Formula(['~', negated_formula[0]]):
                                    return derivation
                            if Formula(['~', negated_formula[2]]) not in formulas_list2:
                                formulas_list2.append(Formula(['~', negated_formula[2]]))
                                derivation.append(NaturalDeductionStep(content=Formula(['~', negated_formula[2]]),
                                                                       justification="DM",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == Formula(['~', negated_formula[2]]):
                                    return derivation
                            applied_rules['DM'].append(formulas_list.index(formula))
                            modif = True
                    # If negating a conjunction, apply DeMorgan2
                    if len(negated_formula) == 3 and negated_formula[0] == '∧':
                        if formulas_list.index(formula) not in applied_rules['DM2']:
                            neg_disjunction = Formula(['∨', ['~', negated_formula[1]], ['~', negated_formula[2]]])
                            if neg_disjunction not in formulas_list2:
                                formulas_list2.append(neg_disjunction)
                                derivation.append(NaturalDeductionStep(content=neg_disjunction,
                                                                       justification="DM2",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == neg_disjunction:
                                    return derivation
                            applied_rules['DM2'].append(formulas_list.index(formula))
                            modif = True
                    # If negating a conditional, apply NegCond (i.e. ~(A → B) |- A and ~(A → B) |- ~B)
                    elif len(negated_formula) == 3 and negated_formula[0] == '→':
                        if formulas_list.index(formula) not in applied_rules['NegCond']:
                            if negated_formula[1] not in formulas_list2:
                                formulas_list2.append(negated_formula[1])
                                derivation.append(NaturalDeductionStep(content=negated_formula[1],
                                                                       justification="NegCond",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == negated_formula[1]:
                                    return derivation
                            if Formula(['~', negated_formula[2]]) not in formulas_list2:
                                formulas_list2.append(Formula(['~', negated_formula[2]]))
                                derivation.append(NaturalDeductionStep(content=Formula(['~', negated_formula[2]]),
                                                                       justification="NegCond",
                                                                       on_steps=self.steps([formulas_list.index(formula)],
                                                                                           jump_steps),
                                                                       open_suppositions=copy(open_sups)))
                                if goal == Formula(['~', negated_formula[2]]):
                                    return derivation
                            applied_rules['NegCond'].append(formulas_list.index(formula))
                            modif = True
                    # See if you can apply E~
                    for formula2 in formulas_list:
                        # If the two formulas are contradictory, derive Falsum
                        if formula2 == negated_formula:
                            if (formulas_list.index(formula), formulas_list.index(formula2)) not in applied_rules['E~']:
                                if Formula(['⊥']) not in formulas_list2:
                                    formulas_list2.append(Formula(['⊥']))
                                    derivation.append(NaturalDeductionStep(content=Formula(['⊥']),
                                                                           justification="E~",
                                                                           on_steps=self.steps([formulas_list.index(formula),
                                                                                        formulas_list.index(formula2)],
                                                                                        jump_steps),
                                                                           open_suppositions=copy(open_sups)))
                                    # If you derive ⊥, return
                                    return derivation
                                applied_rules['E~'].append((formulas_list.index(formula), formulas_list.index(formula2)))
                                modif = True

        # When it reaches here, it has exited the loop (not made any modifications during an iteration)
        return derivation

    # ------------------------------------------------------------------------------------------------------------------
    # ------------------------------------------------------------------------------------------------------------------

    def clean_derivation(self, derivation, inference):
        """Enumerates the steps, deletes unnecessary lines, etc."""

        # First, delete steps not used to reach the conclusion
        used_steps = self.get_used_steps(derivation, inference)
        derivation = self.delete_unused_steps(derivation, used_steps)

        # Second, replace the derived rules with their hardcoded demonstration
        derivation = self.replace_derived_rules(derivation)

        return derivation

    @staticmethod
    def get_used_steps(derivation, inference):
        """Returns a list of the steps that were used to reach the conclusion"""
        used_steps = {}
        # The loop goes backwards from the last step to the first
        for step_number in range(len(derivation)-1, -1, -1):
            # If you find the conclusion outside of any supposition, start registering from there
            if derivation[step_number].content == inference.conclusion and not derivation[step_number].open_suppositions:
                used_steps = {step_number}
            if step_number in used_steps:
                used_steps.update(set(derivation[step_number].on_steps))

        return sorted(list(used_steps))

    def delete_unused_steps(self, derivation, used_steps):
        derivation2 = Derivation([])
        jump_steps = list()
        step_number = 0
        for step in derivation:
            if step_number in used_steps:
                derivation2.append(
                    NaturalDeductionStep(content=step.content, justification=step.justification,
                                         on_steps=self.steps(step.on_steps, jump_steps),
                                         open_suppositions=self.steps(step.open_suppositions, jump_steps))
                )
            else:
                jump_steps.append([step_number, -1])
            step_number += 1

        return derivation2

    # ------------------------------------------------------------------------------------------------------------------

    def replace_derived_rules(self, derivation):
        """Replaces DM2, DM, NegCond, MT and SD with their hardcoded derivation"""

        derivation2 = Derivation([])
        jump_steps2 = list()
        # In the first pass it replaces only DM2 (since DM2 uses DM)
        for step_number in range(len(derivation)):
            # Rebuild the current step to jump the necessary ones (from previously on the loop) (se below) ***
            step = NaturalDeductionStep(content=derivation[step_number].content,
                                        justification=derivation[step_number].justification,
                                        on_steps=self.steps(derivation[step_number].on_steps, jump_steps2),
                                        open_suppositions=self.steps(derivation[step_number].open_suppositions,
                                                                     jump_steps2))
            beginning_step = len(derivation2)  # Not the step_number of the original derivation, but the actual one

            if step.justification == "DM2":
                # A DM2 step has structure :
                # content=Formula(['∨', [~, [A]], [~, [B]]), justification='DM2', on_steps=[a], open_suppositions=[b,c]
                open_sups = copy(step.open_suppositions)
                disjunction = step.content
                negated_conjunction = derivation2[step.on_steps[0]].content

                # Suppose the negation of the disjunction that we want to prove
                open_sups.append(beginning_step)
                derivation2.append(NaturalDeductionStep(content=Formula(['~', disjunction]), justification='supposition',
                                                        on_steps=[], open_suppositions=open_sups))  # Sup ~(~A ∨ ~B)
                # By the other DeMorgan rule, conclude ~~A and ~~B
                derivation2.append(NaturalDeductionStep(content=Formula(['~', disjunction[1]]), justification='DM',
                                                        on_steps=[len(derivation2)-1], open_suppositions=open_sups))
                                                        # len(derivation2)-1 is the line above
                                                        # (current last step of deriv2)
                derivation2.append(NaturalDeductionStep(content=Formula(['~', disjunction[2]]), justification='DM',
                                                        on_steps=[len(derivation2)-2], open_suppositions=open_sups))
                # Eliminate the double negations and get A and B
                derivation2.append(NaturalDeductionStep(content=disjunction[1][1], justification='~~',
                                                        on_steps=[len(derivation2)-2], open_suppositions=open_sups))
                derivation2.append(NaturalDeductionStep(content=disjunction[2][1], justification='~~',
                                                        on_steps=[len(derivation2)-2], open_suppositions=open_sups))
                # Put them in conjunction and get A ∧ B
                # the content is because negated conjunction is ['~', ['∧', A, B]]
                derivation2.append(NaturalDeductionStep(content=negated_conjunction[1], justification='I∧',
                                                        on_steps=[len(derivation2)-2, len(derivation2)-1],
                                                        open_suppositions=open_sups))
                # This gives us a contradiction with ~(A ∧ B) - the formula to which we applied DM2 originally
                derivation2.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                        on_steps=[step.on_steps[0], len(derivation2)-1],
                                                        open_suppositions=open_sups))
                # What follows is just negation introductions and double negation
                open_sups = open_sups[:-1]
                derivation2.append(NaturalDeductionStep(content=Formula(['~', ['~', disjunction]]), justification='I~',
                                                        on_steps=[beginning_step, len(derivation2)-1],
                                                        open_suppositions=open_sups))
                derivation2.append(NaturalDeductionStep(content=disjunction, justification='~~',
                                                        on_steps=[len(derivation2)-1], open_suppositions=open_sups))

                # We've added a bunch of steps (8 before the disjunction),
                # so the following ones in the derivation need to be adjusted (see above) ***
                jump_steps2.append([step_number, 8])

            else:
                # Rebuild the current step to jump the necessary ones (from previously on the loop)
                derivation2.append(step)

        # Second pass: The rest of the rules
        derivation3 = Derivation([])
        jump_steps3 = list()
        for step_number in range(len(derivation2)):
            # Rebuild the current step to jump the necessary ones (from previously on the loop) (se below) ***
            step = NaturalDeductionStep(content=derivation2[step_number].content,
                                        justification=derivation2[step_number].justification,
                                        on_steps=self.steps(derivation2[step_number].on_steps, jump_steps3),
                                        open_suppositions=self.steps(derivation2[step_number].open_suppositions,
                                                                     jump_steps3))
            beginning_step = len(derivation3)  # Not the step_number of the original derivation, but the actual one
            open_sups = copy(step.open_suppositions)

            if step.justification == "DM":
                # A DM step has structure :
                # content=Formula([[~,[A]]), justification='DM', on_steps=[a], open_suppositions=[b,c]
                # A can be either the left or right negated disjunct - e.g. ~(A ∨ B) or ~(B ∨ A)
                negated_disjunct = step.content
                disjunct = negated_disjunct[1]
                negated_disjunction = derivation3[step.on_steps[0]].content
                disjunction = negated_disjunction[1]

                # Suppose A
                open_sups.append(beginning_step)
                derivation3.append(NaturalDeductionStep(content=disjunct, justification='supposition', on_steps=[],
                                                        open_suppositions=open_sups))
                # Introduce disjunction to get A ∨ B  -- or B ∨ A
                derivation3.append(NaturalDeductionStep(content=disjunction, justification='I∨',
                                                        on_steps=[len(derivation3)-1], open_suppositions=open_sups))
                # Get a contradiction with ~(A ∨ B)
                derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                        on_steps=[step.on_steps[0], len(derivation3)-1],
                                                        open_suppositions=open_sups))
                # By negation introduction get the negated disjunct
                derivation3.append(NaturalDeductionStep(content=negated_disjunct, justification='I~',
                                                        on_steps=[beginning_step, len(derivation3)-1],
                                                        open_suppositions=open_sups[:-1]))
                jump_steps3.append([step_number, 3])

            elif step.justification == "NegCond":
                # A NegCond step has structure of either:
                # content=Formula([A]), justification='NegCond', on_steps=[a], open_suppositions=[b,c]
                # content=Formula([~[B]]), justification='NegCond', on_steps=[a], open_suppositions=[b,c]
                negated_conditional = derivation3[step.on_steps[0]].content
                conditional = negated_conditional[1]
                antecedent = conditional[1]
                consequent = conditional[2]

                if step.content == antecedent:
                    # Suppose the negation of the antecedent (~A)
                    open_sups.append(beginning_step)
                    derivation3.append(NaturalDeductionStep(content=Formula(['~', antecedent]), justification='supposition',
                                                            on_steps=[], open_suppositions=open_sups))
                    # Build a conditional (A → B) using Ex Falsum
                    open_sups2 = open_sups + [beginning_step + 1]  # do this instead of append, not modify the prev step
                    derivation3.append(NaturalDeductionStep(content=antecedent, justification='supposition',
                                                            on_steps=[], open_suppositions=open_sups2))
                    derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                            on_steps=[len(derivation3)-2, len(derivation3)-1],
                                                            open_suppositions=open_sups2))
                    derivation3.append(NaturalDeductionStep(content=consequent, justification='EFSQ',
                                                            on_steps=[len(derivation3)-1],
                                                            open_suppositions=open_sups2))
                    derivation3.append(NaturalDeductionStep(content=conditional, justification='I→',
                                                            on_steps=[beginning_step+1, len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    # Get a contradiction with the negated conditional
                    derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                            on_steps=[step.on_steps[0], len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    # Introduce negation and eliminate double negation
                    open_sups = open_sups[:-1]
                    derivation3.append(NaturalDeductionStep(content=Formula(['~', ['~', antecedent]]),
                                                            justification='I~',
                                                            on_steps=[beginning_step, len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    derivation3.append(NaturalDeductionStep(content=antecedent, justification='~~',
                                                            on_steps=[len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    jump_steps3.append([step_number, 7])

                elif step.content == Formula(['~', consequent]):
                    # Suppose the consequent B (we want to obtain ~B)
                    open_sups.append(beginning_step)
                    derivation3.append(NaturalDeductionStep(content=consequent, justification='supposition',
                                                            on_steps=[], open_suppositions=open_sups))
                    # Build the conditional (A → B) using Repetition
                    open_sups2 = open_sups + [beginning_step + 1]  # do this instead of append, not modify the prev step
                    derivation3.append(NaturalDeductionStep(content=antecedent, justification='supposition',
                                                            on_steps=[], open_suppositions=open_sups2))
                    derivation3.append(NaturalDeductionStep(content=consequent, justification='repetition',
                                                            on_steps=[beginning_step],open_suppositions=open_sups2))
                    derivation3.append(NaturalDeductionStep(content=conditional, justification='I→',
                                                            on_steps=[beginning_step+1, len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    # Get a contradiction with the negated conditional
                    derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                            on_steps=[step.on_steps[0], len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    # Negate the original supposition
                    open_sups = open_sups[:-1]
                    derivation3.append(NaturalDeductionStep(content=Formula(['~', consequent]), justification='I~',
                                                            on_steps=[beginning_step, len(derivation3)-1],
                                                            open_suppositions=open_sups))
                    jump_steps3.append([step_number, 5])

            elif step.justification == "MT":
                # A MT step has structure:
                # content=Formula([~,[A]]), justification='MT', on_steps=[a, b], open_suppositions=[c,d]
                # Steps a and b may be A → B, ~B; or A → ~B, B (the conditional always comes first --see above)
                negated_antecedent = step.content
                antecedent = negated_antecedent[1]
                conditional = derivation3[step.on_steps[0]].content
                consequent = conditional[2]
                independent_formula = derivation3[step.on_steps[1]].content  # (may be either ~B or B)

                # Suppose the antecedent A
                open_sups.append(beginning_step)
                derivation3.append(NaturalDeductionStep(content=antecedent, justification='supposition', on_steps=[],
                                                        open_suppositions=open_sups))
                # Get the consequent via Conditional elimination (may be B or ~B)
                derivation3.append(NaturalDeductionStep(content=consequent, justification='E→',
                                                        on_steps=[step.on_steps[0], len(derivation3)-1],
                                                        open_suppositions=open_sups))
                # Get a contradiction with the independent formula (may be ~B or B, respectively to above)
                derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                        on_steps=[step.on_steps[1], len(derivation3)-1],
                                                        open_suppositions=open_sups))
                # Negate the antecedent
                derivation3.append(NaturalDeductionStep(content=negated_antecedent, justification='I~',
                                                        on_steps=[beginning_step, len(derivation3)-1],
                                                        open_suppositions=open_sups[:-1]))
                jump_steps3.append([step_number, 3])

            elif step.justification == "SD":
                # An SD step has two possible structures:
                # content=Formula([A]), justification='SD', on_steps=[a, b], open_suppositions=[c,d]
                # Where steps a and be may be [A ∨ B, ~B] or [B ∨ A, ~B] or [A ∨ ~B, B] or [~B ∨ A, B]
                # The disyunction is always first in the list of on_steps (see above)
                disjunction = derivation3[step.on_steps[0]].content
                derived_disjunct = step.content
                independent_formula = derivation3[step.on_steps[1]].content  # Unnecesary but leave it just in case

                # We are going to do a disjunction elimination, so we will suppose both disjuncts
                # and get two conditionals: A → A and either B → A or ~B → A
                disjunction_elimination_steps = [step.on_steps[0]]
                steps_to_jump = 0  # Do it like this because if both disjuncts are equal (p v p) will jump 1 less step
                for numdisj in (1, 2):
                    open_sups2 = open_sups + [len(derivation3)]
                    derivation3.append(NaturalDeductionStep(content=disjunction[numdisj], justification='supposition',
                                                            on_steps=[], open_suppositions=open_sups2))
                    steps_to_jump += 1
                    if disjunction[numdisj] == derived_disjunct:
                        # If the disjunct (supposed above) is A, repeat it
                        derivation3.append(NaturalDeductionStep(content=derived_disjunct, justification='repetition',
                                                                on_steps=[len(derivation3)-1],
                                                                open_suppositions=open_sups2))
                        # And introduce the conditional
                        derivation3.append(NaturalDeductionStep(content=Formula(['→', derived_disjunct,
                                                                                 derived_disjunct]),
                                                                justification='I→',
                                                                on_steps=[len(derivation3)-2, len(derivation3)-1],
                                                                open_suppositions=open_sups))
                        steps_to_jump += 2
                        disjunction_elimination_steps.append(len(derivation3)-1)
                    else:
                        # If the disjunct (supposed above) is either B or ~B, get Falsum with the independent formula
                        derivation3.append(NaturalDeductionStep(content=Formula(['⊥']), justification='E~',
                                                                on_steps=[step.on_steps[1], len(derivation3)-1],
                                                                open_suppositions=open_sups2))
                        derivation3.append(NaturalDeductionStep(content=derived_disjunct, justification='EFSQ',
                                                                on_steps=[len(derivation3)-1],
                                                                open_suppositions=open_sups2))
                        # Introduce the conditional
                        derivation3.append(NaturalDeductionStep(content=Formula(['→', disjunction[numdisj],
                                                                                 derived_disjunct]),
                                                                justification='I→',
                                                                on_steps=[len(derivation3)-3, len(derivation3)-1],
                                                                open_suppositions=open_sups))
                        steps_to_jump += 3
                        disjunction_elimination_steps.append(len(derivation3) - 1)

                # Eliminate the disjunction with the two conditionals we just built
                derivation3.append(NaturalDeductionStep(content=derived_disjunct, justification='E∨',
                                                        on_steps=disjunction_elimination_steps,
                                                        open_suppositions=open_sups))

                jump_steps3.append([step_number, steps_to_jump])  # The fist supposition counts twice

            else:
                derivation3.append(step)

        return derivation3

    # ------------------------------------------------------------------------------------------------------------------
    # ------------------------------------------------------------------------------------------------------------------
    # Auxiliary functions

    @staticmethod
    def steps(step_list, jump_steps):
        """Basically for conjunction introduction. Given a step list and jump_steps (of the form [[a, b], [c, d]])
        It takes the step list and sums b to every step equal or greater than a, d to every step equal or greater than c
        """
        if jump_steps is None:
            return step_list
        new_step_list = list()
        for step in step_list:
            new_step = step
            for jump in jump_steps:
                if step >= jump[0]:
                    new_step += jump[1]
            new_step_list.append(new_step)
        return new_step_list


classical_natural_deduction_solver = ClassicalNaturalDeductionSolver()
