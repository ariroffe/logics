from copy import copy, deepcopy

from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories import Derivation, NaturalDeductionStep
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants_nobiconditional \
    as cl_language
from logics.classes.exceptions import SolverError


class NaturalDeductionSolver:
    """A heuristic solver for natural deduction

    Works by doing a combination of heuristic reasoning (e.g. if you need to derive a conditional, suppose its
    antecedent and try to reach its consequent) and blind derivation. Blind derivation works with *simplification*
    rules only, i.e. rules that do not add new formulae to their conclusion. These can be primitive or derived. In the
    second case, you should provide a hardcoded derivation of the derived rule, so that after the solver is finished,
    the steps where that rule is used are replaced with their derivation using only primitive rules.

    Parameters
    ----------
    language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        The language of the system
    simplification_rules: dict of {str: logics.classes.propositional.Inference}
        The strings are the rule names, the values are *inferences* (not NaturalDeductionRule) that can function as
        *elimination* rules (they must not contain anything new in the conclusion)
    derived_rules_derivations: dict of {str: logics.classes.propositional.proof_theories.Derivation}
        If among the simplification rules there are some derived rules, and in the final output you wish to replace
        their application with subderivations using only primitive rules, you can use this dict. The keys are the names
        of the rules, the values are derivations of the derived rule. See below for some examples.
    heuristics: list of logics.utils.solvers.natural_deduction.Heuristic
        A list of heuristics to apply (see below). Will be applied in the order they are given in the list.

    Examples
    --------
    Most of the time you will be using the predefined classical solver instance and its `solve` method, as follows:

    >>> from logics.utils.solvers import classical_natural_deduction_solver
    >>> classical_natural_deduction_solver.solve(classical_parser.parse("A → B, ~B / ~A"))
    0. ['→', ['A'], ['B']]; premise; []
    1. ['~', ['B']]; premise; []
    |  2. ['A']; supposition; []
    |  3. ['B']; E→; [0, 2]
    |  4. ['⊥']; E~; [1, 3]
    5. ['~', ['A']]; I~; [2, 4]

    If you want to define your own solver instance, you can do that in the following way. For illustration, we will
    define a toy solver that uses only conjunction elimination and idempotence for disjunction as its simplification
    rules, and has only conjunction heuristics

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants_nobiconditional as cl_language
    >>> from logics.utils.solvers.natural_deduction import NaturalDeductionSolver
    >>> from logics.utils.solvers.natural_deduction import conjunction_heuristic  # See below for more on heuristics
    >>> simplification_rules = {
    ...     # Primitive rules
    ...     'E∧1': classical_parser.parse('A ∧ B / A'),
    ...     'E∧2': classical_parser.parse('A ∧ B / B'),
    ...     # Derived rules
    ...     'IdemDisj': classical_parser.parse('A ∨ A / A')
    ... }
    >>> # Since we have used the non-primitive IdemDisj above, we need to give a hardcoded derivation for it
    ... derived_rules_derivations = {'IdemDisj': classical_parser.parse_derivation('''
    ... A ∨ A; premise; []; []
    ... A; supposition; []; [1]
    ... A; repetition; [1]; [1]
    ... (A → A); I→; [1, 2]; []
    ... (A → A); repetition; [3]; []
    ... A; E∨; [0, 3, 4]; []''', natural_deduction=True)}
    >>> toy_natural_deduction_solver = NaturalDeductionSolver(language=cl_language,
    ...                                                       simplification_rules=simplification_rules,
    ...                                                       derived_rules_derivations=derived_rules_derivations,
    ...                                                       heuristics=[conjunction_heuristic])

    We can now begin deriving things with our new solver

    >>> toy_natural_deduction_solver.solve(classical_parser.parse("A ∧ (B ∧ (C ∨ C)) / C"))
    0. ['∧', ['A'], ['∧', ['B'], ['∨', ['C'], ['C']]]]; premise; []
    1. ['∧', ['B'], ['∨', ['C'], ['C']]]; E∧2; [0]
    2. ['∨', ['C'], ['C']]; E∧2; [1]
    |  3. ['C']; supposition; []
    |  4. ['C']; repetition; [3]
    5. ['→', ['C'], ['C']]; I→; [3, 4]
    6. ['→', ['C'], ['C']]; repetition; [5]
    7. ['C']; E∨; [2, 5, 6]
    """
    # Works as follows. Given an inference to the ``solve`` method:
    #
    # * If the goal (conclusion) has already been reached (is among the premises) exits
    # * Otherwise, blindly derives everything it can with a set of *elimination* rules (some primitive, some derived),
    #   from the premises given, and checks again for the goal
    # * If it still did not reach the goal, applies heuristics. Each heuristic will do the following:
    #
    #   - Analyze the goal and see if the heuristic is applicable (e.g. conditional heuristic is applicable only if
    #     the goal is a conditional formula)
    #   - Add something to the derivation (e.g. if the goal is a conditional add a supposition of the antecedent).
    #     Some heuristics (e.g. conjunction heuristic) will not add anything
    #   - Call the ``solve`` method recursively with a new goal (e.g. the consequent) and new premises (everything in
    #     the derivation up to that point)
    #   - If it finds the derivation, applies an *introduction* rule after it (e.g. conditional introduction)
    #   - (see below for the documentation on heuristics)
    #
    # * Also has some sub-algorithms for cleaning the derivation afterwards (deleting unnecesary steps, replacing the
    #   applications of derived rules for derivations with only primitive rules, etc.)

    exit_on_falsum = True  # For the _apply_simplification_rules, will stop blindly deriving if it finds falsum
    def __init__(self, language, simplification_rules, derived_rules_derivations, heuristics):
        """
        Simplification rules is a dictionary, key is the name of the rule, value is an Inference (see apply_rule below)
        """
        self.language = language
        self.simplification_rules = simplification_rules
        self.derived_rules_derivations = derived_rules_derivations
        self.heuristics = heuristics

    def solve(self, inference):
        """Takes an Inference and returns a derivation for it

        Examples
        --------
        See above for an example using the predefined classical solver instance
        """
        goal = inference.conclusion
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inference.premises])
        derivation = self._solve_derivation(derivation, goal)   # Actually solves the derivation (using some derived rules)
        derivation = self._clean_derivation(derivation, inference)  # Erases unnecesary steps and replaces derived rules
        return derivation

    # ------------------------------------------------------------------------------------------------------------------

    def _solve_derivation(self, derivation, goal, tried_existentials=None):
        """First of the two algorithms of the solver, basically does the following:
        - First, checks is the goal is already present
        - If not, blindly derives things using elimination rules (some of them derived)
        - If it still did not find the goal, analizes the goal and sets a new goal using heuristics, may add things as
          suppositions in the process
        """
        # The goal is already present in the derivation (and not in a closed supposition), return it
        current_open_sups = self._get_current_open_sups(derivation)
        for step_idx in range(len(derivation)):
            if not self._is_in_closed_supposition(derivation[step_idx].open_suppositions, current_open_sups) and \
                    derivation[step_idx].content == goal:
                return derivation

        # Apply simplification rules (elimination + a couple more, see below)
        derivation = self._apply_simplification_rules(derivation, goal)

        # The goal has been reached by the application of the rules
        # (the second algorithm exits if it finds the goal, so the goal should be in the last step)
        if derivation and derivation[-1].content == goal:
            return derivation

        # This is for the predicate solver and the existential elimination heuristic
        if tried_existentials is None:
            tried_existentials = []

        # If it did not find the goal, apply heuristics (they might call this method recursively)
        for heuristic in self.heuristics:
            if heuristic.is_applicable(goal):
                try:
                    return heuristic.apply_heuristic(derivation, goal, self, tried_existentials)
                except SolverError:
                    pass

        # If you did not return thus far (goal should be ⊥), raise an exception
        else:
            raise SolverError('Could not solve the derivation provided')

    # ------------------------------------------------------------------------------------------------------------------

    def _apply_simplification_rules(self, derivation, goal):
        """Blindly derives everything it can but using only rules that simplify formulae, some of them derived
        (not things like I∨, which would be impossible to apply blindly)

        Makes changes and records the indexes on applied_rules (so that it doesn't repeat them)
        When it has no more changes to make (modif = False), returns
        """
        # If the derivation is empty (inference with no premises), there is nothing to do here
        if not derivation:
            return derivation

        # initialization, parameters we will need inside the loop
        applied_rules = {rule_name: [] for rule_name in self.simplification_rules}
        open_sups = derivation[-1].open_suppositions  # None of the simplif rules open sups, so this can remain the same
        prev_len_derivation = 0  # zero initially so that it enters the first loop below
        formulas_list = [step.content for step in derivation]  # will be needed below to not repeat adding

        while prev_len_derivation != len(derivation):  # When they are equal we have not added any new steps
            prev_len_derivation = len(derivation)

            # For each step in the derivation, see if we can apply a rule to it (if it is the first premise of the rule)
            for step_idx, step in enumerate(derivation):
                # Check that the step is not in a closed supposition
                if self._is_in_closed_supposition(step.open_suppositions, open_sups):
                    continue

                for rule_name in self.simplification_rules:
                    # Check that the rule has not been applied to this step before
                    if step_idx in applied_rules[rule_name]:
                        continue

                    rule = self.simplification_rules[rule_name]

                    # See if the current formula being examined is an instance of the first premise of the rule
                    first_premise_is_instance, subst_dict = step.content.is_instance_of(rule.premises[0],
                                                                                        self.language,
                                                                                        return_subst_dict=True)
                    if first_premise_is_instance:
                        rule_steps = [step_idx]

                        # Check if the rest of the premises are present
                        rest_of_premises_present = True
                        for premise in rule.premises[1:]:
                            premise_present = False

                            # Go over each formula in the derivation again
                            for step_idx2, step2 in enumerate(derivation):
                                # Again, check that this step is not in a closed supposition
                                if self._is_in_closed_supposition(step2.open_suppositions, open_sups):
                                    continue

                                premise_is_instance, subst_dict = step2.content.is_instance_of(premise,
                                                                                            self.language,
                                                                                            subst_dict=subst_dict,
                                                                                            return_subst_dict=True)
                                if premise_is_instance:
                                    premise_present = True
                                    rule_steps.append(step_idx2)
                                    break  # Do not keep looking for this rule premise once we found it

                            if not premise_present:
                                rest_of_premises_present = False
                                break

                        # If the rest of the premises are present, we can apply the rule
                        if rest_of_premises_present:
                            # Get what the instance/s of the conclusion would look like
                            # Is a list bc the predicate solver sometimes adds multiple formulae at once (e.g. E∀)
                            formulae_to_add = self._get_formulae_to_add(rule.conclusions[0], subst_dict)
                            for formula_to_add in formulae_to_add:
                                # Check if the conclusion is not already in the derivation (avoids freezing), add it
                                if formula_to_add not in formulas_list:
                                    formulas_list.append(formula_to_add)
                                    derivation.append(NaturalDeductionStep(content=formula_to_add,
                                                                           justification=rule_name,
                                                                           on_steps=rule_steps,
                                                                           open_suppositions=copy(open_sups)))
                                    if goal == formula_to_add:
                                        return derivation
                                    if self.exit_on_falsum and formula_to_add == Formula(['⊥']):
                                        return derivation

                                    # Register that we applied this rule to this step, so that we don't repeat
                                    if step_idx not in applied_rules[rule_name]:
                                        applied_rules[rule_name].append(step_idx)

        # When it reaches here, it has exited the loop (not made any modifications during an iteration)
        return derivation

    def _get_formulae_to_add(self, rule_conclusion, subst_dict):
        # Overriden in the predicate solver
        return [rule_conclusion.instantiate(self.language, subst_dict)]

    # ------------------------------------------------------------------------------------------------------------------
    # ------------------------------------------------------------------------------------------------------------------
    # Methods for cleaning the derivation and presenting it in a prettier way to the user

    def _clean_derivation(self, derivation, inference):
        """Enumerates the steps, deletes unnecessary lines, etc."""

        # First, delete steps not used to reach the conclusion
        used_steps = self._get_used_steps(derivation, inference)
        derivation = self._delete_unused_steps(derivation, used_steps)

        # Second, replace the derived rules with their hardcoded demonstration
        derivation = self._replace_derived_rules(derivation, self.derived_rules_derivations)

        return derivation

    @staticmethod
    def _get_used_steps(derivation, inference):
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

    def _delete_unused_steps(self, derivation, used_steps):
        derivation2 = Derivation([])
        jump_steps = list()
        step_number = 0
        for step in derivation:
            if step_number in used_steps:
                derivation2.append(
                    NaturalDeductionStep(content=step.content, justification=step.justification,
                                         on_steps=self._steps(step.on_steps, jump_steps),
                                         open_suppositions=self._steps(step.open_suppositions, jump_steps))
                )
            else:
                jump_steps.append([step_number, -1])
            step_number += 1

        return derivation2

    # ------------------------------------------------------------------------------------------------------------------

    def _replace_derived_rules(self, derivation, hardcoded_rules):
        """Replaces the derived rule steps with their hardcoded derivation"""

        derivation2 = Derivation([])
        jump_steps2 = list()
        for step_number in range(len(derivation)):
            # Rebuild the current step to jump the necessary ones (from previously on the loop)
            # (when a derived rule is present, it will add steps to the derivation, so the on_steps and
            # open_suppositions will not correspond to the ones present in derivation2)
            step = NaturalDeductionStep(content=derivation[step_number].content,
                                        justification=derivation[step_number].justification,
                                        on_steps=self._steps(derivation[step_number].on_steps, jump_steps2),
                                        open_suppositions=self._steps(derivation[step_number].open_suppositions,
                                                                     jump_steps2))
            beginning_step = len(derivation2)  # Not the step_number of the original derivation, but the actual one
            open_sups = copy(step.open_suppositions)
            on_steps_iterator = iter(step.on_steps)

            derived_rule = False
            for derived_rule_name in hardcoded_rules:
                if step.justification == derived_rule_name:
                    derived_rule = True
                    derived_rule_derivation = hardcoded_rules[derived_rule_name]
                    step_correspondence_dict = dict()
                    new_jump_steps = 0  # How many you will jump by adding the derivation of this rule
                    num_premises = 0

                    # Look at the current step and check that it is an instance of the conclusion of the derivation
                    instance, subst_dict = step.content.is_instance_of(derived_rule_derivation[-1].content,
                                                                       self.language,
                                                                       return_subst_dict=True)
                    if not instance:
                        raise SolverError(f"Formula {step.content} is not an instance of the derived rule's conclusion")

                    # Go step by step in the derivation of the derived rule
                    step2_index = -1
                    for step2 in derived_rule_derivation:
                        step2_index += 1

                        # If the step is a premise in the derivation of the derived rule, it is because it must be
                        # present before in the current derivation
                        if step2.justification == 'premise':
                            # Since the other algorithms build the on_steps in order, we know that the first on_step
                            # will correspond to the first premise of the derived rule derivation, the second with the
                            # second, and so on. Thus, we can do this with an iterator.
                            prev_step_index = next(on_steps_iterator)
                            prev_step_formula = derivation2[prev_step_index].content

                            # Get the substitution dictionary (for later steps)
                            is_instance_of_formula, subst_dict = prev_step_formula.is_instance_of(step2.content,
                                                                                                  self.language,
                                                                                                  subst_dict=subst_dict,
                                                                                                  return_subst_dict=True)
                            if not is_instance_of_formula:
                                raise SolverError(f'Formula {prev_step_formula} not an instance of {step2.content}')

                            # Update the step_correspondence dict
                            step_correspondence_dict[step2_index] = prev_step_index
                            num_premises += 1

                        # If the step is not a premise, then it is a new step in the derivation and we need to add it
                        else:
                            # Get the new content
                            new_formula = self._get_non_premise_replacement(step2.content, subst_dict, derivation2)

                            step_correspondence_dict[step2_index] = len(derivation2)

                            new_on_steps = [step_correspondence_dict[x] for x in step2.on_steps]
                            new_open_sups = open_sups + [step_correspondence_dict[x] for x in step2.open_suppositions]

                            derivation2.append(NaturalDeductionStep(content=new_formula,
                                                                    justification=step2.justification,
                                                                    on_steps=new_on_steps,
                                                                    open_suppositions=new_open_sups))
                            new_jump_steps += 1

                    jump_steps2.append([beginning_step, new_jump_steps-1])  # -1 bc the derived step is still present
                    break  # Do not keep looking at the rest of the derived rules

            if not derived_rule:
                derivation2.append(step)

        return derivation2

    def _get_non_premise_replacement(self, hardcoded_derivation_step, subst_dict, derivation):
        # Overriden in the predicate solver
        return hardcoded_derivation_step.instantiate(self.language, subst_dict)  # instantiate returns a deepcopy

    # ------------------------------------------------------------------------------------------------------------------
    # ------------------------------------------------------------------------------------------------------------------
    # Auxiliary functions

    @staticmethod
    def _get_current_open_sups(derivation):
        current_open_sups = list()
        if derivation:
            current_open_sups = derivation[-1].open_suppositions
        return current_open_sups

    @staticmethod
    def _is_in_closed_supposition(step_open_sups, current_open_sups):
        return not set(step_open_sups).issubset(set(current_open_sups))

    def _get_step_of_formula(self, formula, derivation, current_open_sups):
        # get the step number of a given formula, such that the formula is not in a closed supposition
        for index in range(len(derivation)):
            if self._is_in_closed_supposition(derivation[index].open_suppositions, current_open_sups):
                continue
            if derivation[index].content == formula:
                return index
        return None

    @staticmethod
    def _steps(step_list, jump_steps):
        """For replacing derived rules with their derivations, because once you introduce steps in the middle you have
        to change the ones that come after it.

        Given a step list and jump_steps (of the form [[a, b], [c, d]]):
        - Takes the step list and sums b to every step equal or greater than a
        - d to every step equal or greater than c
        - etc.
        """
        if jump_steps is None:
            return step_list
        new_step_list = list()
        for step in step_list:
            new_step = step
            for jump in jump_steps:
                if max(step, new_step) >= jump[0]:   # The max is so that it works with the -1 jump of delete_unused
                    new_step += jump[1]
            new_step_list.append(new_step)
        return new_step_list


# ------------------------------------------------------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------
# HEURISTICS
# General class and some common ones as subclasses

class Heuristic:
    """ Parent class for defining heuristics.

    To define your own heuristic, inherit from this class and override the `is_applicable` and `apply_heuristic`
    methods.

    Examples
    --------
    See the source code for examples on how to define heuristics.
    """
    def is_applicable(self, goal):
        """Determines whether the heuristic is applicable given the current goal.

        Takes the goal as parameter and should return a boolean.
        The other two parameters are basically for the existential heuristic in the predicate solver
        """
        raise NotImplementedError()

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        """Applies the heuristic.

        Takes the current deriation, goal, current open suppositions and solver, and returns a derivation.
        The parameter `jump_steps` is present because of how the conjunction heuristic works (see the source code for
        the conjunction heuristic for more on this)
        """
        raise SolverError()


class ConjunctionHeuristic(Heuristic):
    """
    Given a goal of the form A ∧ B, solve for A, add the derivation to the current one, and then do the same and solve
    for B; finally, apply conjunction introduction.
    """

    def is_applicable(self, goal):
        return goal.main_symbol == '∧'

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        deriv1 = deepcopy(derivation)
        # Solve the derivation of the first conjunct
        deriv1 = solver._solve_derivation(derivation=deriv1, goal=goal[1])
        open_sups = solver._get_current_open_sups(derivation)

        # Save the step where the first conjunct is, for the introduction later
        # (the step may not be the last of deriv1 if the first conjunct was already present in the derivation)
        first_conjunct_step = solver._get_step_of_formula(goal[1], deriv1, open_sups)

        # If asked for a conjunction between the same two formulas, simply repeat the first conjunct
        # (more efficient, and otherwise p / p ∧ p would have on steps [1, 1] which is wrong)
        if goal[1] == goal[2]:
            deriv1.append(NaturalDeductionStep(content=goal[2], justification="repetition",
                                               on_steps=[first_conjunct_step],
                                               open_suppositions=copy(open_sups)))
            deriv1.append(NaturalDeductionStep(content=goal, justification="I∧",
                                                   on_steps=[first_conjunct_step, len(deriv1) - 1],
                                                   open_suppositions=copy(open_sups)))
            return deriv1

        # Otherwise, if the second conjunct is different from the first, solve the derivation for the second conjunct
        deriv1 = solver._solve_derivation(derivation=deriv1, goal=goal[2])

        # Save the step where the second conjunct is, for the introduction later
        second_conjunct_step = solver._get_step_of_formula(goal[2], deriv1, open_sups)

        deriv1.append(NaturalDeductionStep(content=goal, justification="I∧",
                                           on_steps=[first_conjunct_step, second_conjunct_step],
                                           open_suppositions=copy(open_sups)))
        return deriv1


conjunction_heuristic = ConjunctionHeuristic()


class ConditionalHeuristic(Heuristic):
    def is_applicable(self, goal):
        return goal.main_symbol == '→'

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        deriv1 = deepcopy(derivation)

        # Add the antecedent as a supposition
        prev_open_sups = solver._get_current_open_sups(derivation)
        new_open_sups = prev_open_sups + [len(derivation)]
        deriv1.append(NaturalDeductionStep(content=goal[1], justification='supposition',
                                           on_steps=[], open_suppositions=copy(new_open_sups)))

        # Solve for the consequent
        deriv1 = solver._solve_derivation(derivation=deriv1, goal=goal[2])

        # If deriv1 has one more step (the supposition), it is because the derivation already contained
        # the consequent, and therefore it just returned. We need to repeat the consequent to close it.
        if len(deriv1) == len(derivation)+1:
            consequent_step = solver._get_step_of_formula(goal[2], deriv1, new_open_sups)  # new to check the antecedent
            deriv1.append(NaturalDeductionStep(content=goal[2], justification='repetition',
                                               on_steps=[consequent_step],
                                               open_suppositions=copy(new_open_sups)))

        deriv1.append(NaturalDeductionStep(content=goal, justification="I→",
                                           on_steps=[len(derivation),  # where we introduced the supposition
                                                     len(deriv1)-1],   # last step of the new derivation
                                           open_suppositions=copy(prev_open_sups)))
        return deriv1


conditional_heuristic = ConditionalHeuristic()


class DisjunctionHeuristic(Heuristic):
    def is_applicable(self, goal):
        return goal.main_symbol == '∨'

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        deriv1 = deepcopy(derivation)
        prev_open_sups = solver._get_current_open_sups(derivation)

        # Try to solve for each disjunct separately
        for disjunct in (1, 2):
            try:
                deriv1 = solver._solve_derivation(derivation=deriv1, goal=goal[disjunct])

                # Look for where the disjunct is (may not be the last step if it was present in the derivation)
                step_num = solver._get_step_of_formula(goal[disjunct], deriv1, prev_open_sups)
                deriv1.append(NaturalDeductionStep(content=goal, justification=f'I∨{disjunct}',
                                                       on_steps=[step_num],
                                                       open_suppositions=copy(prev_open_sups)))
                return deriv1
            except SolverError as e:
                if disjunct == 1:
                    pass
                else:
                    raise e


disjunction_heuristic = DisjunctionHeuristic()


class ReductioHeuristic(Heuristic):
    def __init__(self, formula_class=Formula):
        self.formula_class = formula_class

    def is_applicable(self, goal):
        return goal != self.formula_class(['⊥'])

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        deriv1 = deepcopy(derivation)

        # Add the negation of the goal as a supposition
        prev_open_sups = solver._get_current_open_sups(derivation)
        new_open_sups = prev_open_sups + [len(derivation)]
        deriv1.append(NaturalDeductionStep(content=self.formula_class(['~', goal]), justification='supposition',
                                           on_steps=[], open_suppositions=copy(new_open_sups)))

        # Solve for falsum
        new_goal = self.formula_class(['⊥'])
        deriv1 = solver._solve_derivation(derivation=deriv1, goal=new_goal)

        # If deriv1 has one more step (the supposition), it is because the derivation already contained
        # falsum, and therefore it just returned. We need to repeat falsum to close it.
        if len(deriv1) == len(derivation)+1:
            falsum_step = solver._get_step_of_formula(new_goal, deriv1, prev_open_sups)
            deriv1.append(NaturalDeductionStep(content=goal[2], justification='repetition',
                                               on_steps=[falsum_step],
                                               open_suppositions=copy(new_open_sups)))

        deriv1.append(NaturalDeductionStep(content=self.formula_class(['~', ['~', goal]]),
                                           justification="I~",
                                           on_steps=[len(derivation),  # where we introduced the supposition
                                                     len(deriv1)-1],
                                           open_suppositions=copy(prev_open_sups)))
        deriv1.append(NaturalDeductionStep(content=goal, justification="~~",
                                           on_steps=[len(deriv1)- 1],
                                           open_suppositions=copy(prev_open_sups)))
        return deriv1


reductio_heuristic = ReductioHeuristic()


class EFSQHeuristic(Heuristic):
    def __init__(self, formula_class=Formula):
        self.formula_class = formula_class

    def is_applicable(self, goal):
        return True

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        open_sups = solver._get_current_open_sups(derivation)
        falsum_idx = solver._get_step_of_formula(self.formula_class(['⊥']), derivation, open_sups)
        if falsum_idx is not None:
            deriv1 = deepcopy(derivation)
            deriv1.append(NaturalDeductionStep(content=goal, justification='EFSQ',
                                               on_steps=[falsum_idx],
                                               open_suppositions=copy(open_sups)))
            return deriv1
        raise SolverError()


efsq_heuristic = EFSQHeuristic()


# ------------------------------------------------------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------
# INSTANCES

# SIMPLIFICATION RULES WITH WHICH TO DERIVE BLINDLY (may be derived)
standard_simplification_rules = {
    # Primitive rules
    'E∧1': Inference(premises=[Formula(['∧', ['A'], ['B']])],
                     conclusions=[Formula(['A'])]),
    'E∧2': Inference(premises=[Formula(['∧', ['A'], ['B']])],
                     conclusions=[Formula(['B'])]),
    'E→': Inference(premises=[Formula(['→', ['A'], ['B']]), Formula(['A'])],
                    conclusions=[Formula(['B'])]),
    'E∨': Inference(premises=[Formula(['∨', ['A'], ['B']]), Formula(['→', ['A'], ['C']]), Formula(['→', ['B'], ['C']])],
                    conclusions=[Formula(['C'])]),
    'E~': Inference(premises=[Formula(['~', ['A']]), Formula(['A'])],
                    conclusions=[Formula(['⊥'])]),
    '~~': Inference(premises=[Formula(['~', ['~', ['A']]])],
                    conclusions=[Formula(['A'])]),
    # Derived rules
    'MTa': Inference(premises=[Formula(['→', ['A'], ['B']]), Formula(['~', ['B']])],
                     conclusions=[Formula(['~', ['A']])]),
    'MTb': Inference(premises=[Formula(['→', ['A'], ['~', ['B']]]), Formula(['B'])],
                     conclusions=[Formula(['~', ['A']])]),
    'DMa': Inference(premises=[Formula(['~', ['∨', ['A'], ['B']]])],
                     conclusions=[Formula(['~', ['A']])]),
    'DMb': Inference(premises=[Formula(['~', ['∨', ['A'], ['B']]])],
                     conclusions=[Formula(['~', ['B']])]),
    'DMc': Inference(premises=[Formula(['~', ['∧', ['A'], ['B']]])],
                     conclusions=[Formula(['∨', ['~', ['A']], ['~', ['B']]])]),
    'NegConda': Inference(premises=[Formula(['~', ['→', ['A'], ['B']]])],
                          conclusions=[Formula(['A'])]),
    'NegCondb': Inference(premises=[Formula(['~', ['→', ['A'], ['B']]])],
                          conclusions=[Formula(['~', ['B']])]),
    'SDa': Inference(premises=[Formula(['∨', ['A'], ['B']]), Formula(['~', ['A']])],
                     conclusions=[Formula(['B'])]),
    'SDb': Inference(premises=[Formula(['∨', ['A'], ['B']]), Formula(['~', ['B']])],
                     conclusions=[Formula(['A'])]),
    'SDc': Inference(premises=[Formula(['∨', ['~', ['A']], ['B']]), Formula(['A'])],
                     conclusions=[Formula(['B'])]),
    'SDd': Inference(premises=[Formula(['∨', ['A'], ['~', ['B']]]), Formula(['B'])],
                     conclusions=[Formula(['A'])]),
    'IdemDisj': Inference(premises=[Formula(['∨', ['A'], ['A']])],
                          conclusions=[Formula(['A'])]),
    'NeuDisja': Inference(premises=[Formula(['∨', ['A'], ['⊥']])],
                           conclusions=[Formula(['A'])]),
    'NeuDisjb': Inference(premises=[Formula(['∨', ['⊥'], ['A']])],
                           conclusions=[Formula(['A'])]),
    'AbsorDisja': Inference(premises=[Formula(['∨', ['A'], ['∧', ['A'], ['B']]])],
                            conclusions=[Formula(['A'])]),
    'AbsorDisjb': Inference(premises=[Formula(['∨', ['A'], ['∧', ['B'], ['A']]])],
                            conclusions=[Formula(['A'])]),
    'AbsorDisjc': Inference(premises=[Formula(['∨', ['∧', ['A'], ['B']], ['A']])],
                            conclusions=[Formula(['A'])]),
    'AbsorDisjd': Inference(premises=[Formula(['∨', ['∧', ['B'], ['A']], ['A']])],
                            conclusions=[Formula(['A'])]),
}

# HARDCODED DERIVATIONS OF THE DERIVED RULES USED ABOVE
MTa_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['→', ['A'], ['B']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['B']), justification='E→', on_steps=[0, 2], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 3], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='I~', on_steps=[2, 4], open_suppositions=[]),
])
MTb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['→', ['A'], ['~', ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['B']), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='E→', on_steps=[0, 2], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[3, 1], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='I~', on_steps=[2, 4], open_suppositions=[]),
])
DMa_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['~', ['∨', ['A'], ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['B']]), justification='I∨1', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[0, 2], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='I~', on_steps=[1, 3], open_suppositions=[]),
])
DMb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['~', ['∨', ['A'], ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['B']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['B']]), justification='I∨2', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[0, 2], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='I~', on_steps=[1, 3], open_suppositions=[]),
])
DMc_derivation = Derivation([
    # 0
    NaturalDeductionStep(content=Formula(['~', ['∧', ['A'], ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['∨', ['~', ['A']], ['~', ['B']]]]), justification='supposition',
                         open_suppositions=[1]),

    # 2
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='supposition', open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['∨', ['~', ['A']], ['~', ['B']]]), justification='I∨1', on_steps=[2],
                         open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 3], open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['~', ['~', ['A']]]), justification='I~', on_steps=[2, 4],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='~~', on_steps=[5], open_suppositions=[1]),

    # 7
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='supposition', open_suppositions=[1, 7]),
    NaturalDeductionStep(content=Formula(['∨', ['~', ['A']], ['~', ['B']]]), justification='I∨2', on_steps=[7],
                         open_suppositions=[1, 7]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 8], open_suppositions=[1, 7]),
    NaturalDeductionStep(content=Formula(['~', ['~', ['B']]]), justification='I~', on_steps=[7, 9],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['B']), justification='~~', on_steps=[10], open_suppositions=[1]),

    # 12
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['B']]), justification='I∧', on_steps=[6, 11],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[0, 12], open_suppositions=[1]),

    NaturalDeductionStep(content=Formula(['~', ['~', ['∨', ['~', ['A']], ['~', ['B']]]]]), justification='I~',
                         on_steps=[1, 13], open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['∨', ['~', ['A']], ['~', ['B']]]), justification='~~',
                         on_steps=[14], open_suppositions=[]),
])
NegConda_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['~', ['→', ['A'], ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 2], open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['B']), justification='EFSQ', on_steps=[3], open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['B']]), justification='I→', on_steps=[2, 4],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[0, 5], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['~', ['A']]]), justification='I~', on_steps=[1, 6],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='~~', on_steps=[7], open_suppositions=[]),
])
NegCondb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['~', ['→', ['A'], ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['B']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['B']), justification='repetition', on_steps=[1], open_suppositions=[1, 2]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['B']]), justification='I→', on_steps=[2, 3],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[0, 4], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='I~', on_steps=[1, 5],
                         open_suppositions=[]),
])
SDa_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['B']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='premise', open_suppositions=[]),
    # 2
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 2], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['B']), justification='EFSQ', on_steps=[3], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['B']]), justification='I→', on_steps=[2, 4],
                         open_suppositions=[]),
    # 6
    NaturalDeductionStep(content=Formula(['B']), justification='supposition', open_suppositions=[6]),
    NaturalDeductionStep(content=Formula(['B']), justification='repetition', on_steps=[6], open_suppositions=[6]),
    NaturalDeductionStep(content=Formula(['→', ['B'], ['B']]), justification='I→', on_steps=[6, 7],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['B']), justification='E∨', on_steps=[0, 5, 8], open_suppositions=[]),
])
SDb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['B']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='premise', open_suppositions=[]),
    # 2
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[2], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[2, 3],
                         open_suppositions=[]),
    # 5
    NaturalDeductionStep(content=Formula(['B']), justification='supposition', open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[1, 5], open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['A']), justification='EFSQ', on_steps=[6], open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['→', ['B'], ['A']]), justification='I→', on_steps=[5, 7],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 4, 8], open_suppositions=[]),
])
SDc_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['~', ['A']], ['B']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='premise', open_suppositions=[]),
    # 2
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[2, 1], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['B']), justification='EFSQ', on_steps=[3], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['→', ['~', ['A']], ['B']]), justification='I→', on_steps=[2, 4],
                         open_suppositions=[]),
    # 6
    NaturalDeductionStep(content=Formula(['B']), justification='supposition', open_suppositions=[6]),
    NaturalDeductionStep(content=Formula(['B']), justification='repetition', on_steps=[6], open_suppositions=[6]),
    NaturalDeductionStep(content=Formula(['→', ['B'], ['B']]), justification='I→', on_steps=[6, 7],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['B']), justification='E∨', on_steps=[0, 5, 8], open_suppositions=[]),
])
SDd_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['~', ['B']]]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['B']), justification='premise', open_suppositions=[]),
    # 2
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[2], open_suppositions=[2]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[2, 3],
                         open_suppositions=[]),
    # 5
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='supposition', open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['⊥']), justification='E~', on_steps=[5, 1], open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['A']), justification='EFSQ', on_steps=[6], open_suppositions=[5]),
    NaturalDeductionStep(content=Formula(['→', ['~', ['B']], ['A']]), justification='I→', on_steps=[5, 7],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 4, 8], open_suppositions=[]),
])
IdemDisj_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['A']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='repetition', on_steps=[3],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 4], open_suppositions=[]),
])
NeuDisja_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['⊥']]), justification='premise', open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),
    # 4
    NaturalDeductionStep(content=Formula(['⊥']), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='EFSQ', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['⊥'], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])
NeuDisjb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['⊥'], ['A']]), justification='premise', open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['⊥']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='EFSQ', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['⊥'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),

    # 4
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])
AbsorDisja_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['∧', ['A'], ['B']]]), justification='premise',
                         open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),

    # 4
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['B']]), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∧1', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['∧', ['A'], ['B']], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])
AbsorDisjb_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['A'], ['∧', ['B'], ['A']]]), justification='premise',
                         open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),

    # 4
    NaturalDeductionStep(content=Formula(['∧', ['B'], ['A']]), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∧2', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['∧', ['B'], ['A']], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])
AbsorDisjc_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['∧', ['A'], ['B']], ['A']]), justification='premise',
                         open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['B']]), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∧1', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['∧', ['A'], ['B']], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),

    # 4
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])
AbsorDisjd_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∨', ['∧', ['B'], ['A']], ['A']]), justification='premise',
                         open_suppositions=[]),
    # 1
    NaturalDeductionStep(content=Formula(['∧', ['B'], ['A']]), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['A']), justification='E∧2', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['→', ['∧', ['B'], ['A']], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),

    # 4
    NaturalDeductionStep(content=Formula(['A']), justification='supposition', open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['A']), justification='repetition', on_steps=[4], open_suppositions=[4]),
    NaturalDeductionStep(content=Formula(['→', ['A'], ['A']]), justification='I→', on_steps=[4, 5],
                         open_suppositions=[]),

    NaturalDeductionStep(content=Formula(['A']), justification='E∨', on_steps=[0, 3, 6], open_suppositions=[]),
])


standard_derived_rules_derivations = {
    'MTa': MTa_derivation,
    'MTb': MTb_derivation,
    'DMa': DMa_derivation,
    'DMb': DMb_derivation,
    'DMc': DMc_derivation,
    'NegConda': NegConda_derivation,
    'NegCondb': NegCondb_derivation,
    'SDa': SDa_derivation,
    'SDb': SDb_derivation,
    'SDc': SDc_derivation,
    'SDd': SDd_derivation,
    'IdemDisj': IdemDisj_derivation,
    'NeuDisja': NeuDisja_derivation,
    'NeuDisjb': NeuDisjb_derivation,
    'AbsorDisja': AbsorDisja_derivation,
    'AbsorDisjb': AbsorDisjb_derivation,
    'AbsorDisjc': AbsorDisjc_derivation,
    'AbsorDisjd': AbsorDisjd_derivation,
}

classical_natural_deduction_solver = NaturalDeductionSolver(language=cl_language,
                                                        simplification_rules=standard_simplification_rules,
                                                        derived_rules_derivations=standard_derived_rules_derivations,
                                                        heuristics=[efsq_heuristic,
                                                                    conjunction_heuristic,
                                                                    conditional_heuristic,
                                                                    disjunction_heuristic,
                                                                    reductio_heuristic])


# ----------------------------------------------------------------------------
# Classical system 2 (see instances.propositional.natural_deduction)

class AltNaturalDeductionSolver(NaturalDeductionSolver):
    def __init__(self, extra_derived_rules_derivations, *args, **kwargs):
        self.extra_derived_rules_derivations = extra_derived_rules_derivations
        super().__init__(*args, **kwargs)

    def _clean_derivation(self, derivation, inference):
        derivation = super()._clean_derivation(derivation, inference)
        # Before replacing the instances of ESFQ we need to change the justifications (esp for EFSQ, changes content)
        derivation = self._replace_justifications(derivation)
        derivation = self._replace_derived_rules(derivation, self.extra_derived_rules_derivations)
        return derivation

    def _replace_justifications(self, derivation):
        """replace ~~ for E~, E~ for I∧"""
        for step in derivation:
            # Negation elim -> conjunction intro
            if step.justification == "E~" and len(step.on_steps) == 2:
                # Change the content, put the negated formula in second place
                formula1 = derivation[step.on_steps[0]].content
                formula2 = derivation[step.on_steps[1]].content
                if formula2 == Formula(['~', formula1]):
                    # The second formula is the negated one, no need to change the on_steps
                    step.content = Formula(['∧', formula1, formula2])
                elif formula1 == Formula(['~', formula2]):
                    # The first formula is the negated one, invert the on_steps
                    step.content = Formula(['∧', formula2, formula1])
                    step.on_steps = [step.on_steps[1], step.on_steps[0]]
                step.justification = 'I∧'
            # Double negation -> E~
            elif step.justification == '~~':
                step.justification = 'E~'

        return derivation


# Repetition and EFSQ are derived rules in this system
repetition_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['A']), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['A']]), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['~', ['A']]]), justification='I∧', on_steps=[0, 1],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['~', ['A']]]), justification='I~', on_steps=[1, 2],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['A']), justification='E~', on_steps=[3], open_suppositions=[]),
])
EFSQ_derivation = Derivation([
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['~', ['A']]]), justification='premise', on_steps=[],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['~', ['B']]), justification='supposition', on_steps=[],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['∧', ['∧', ['A'], ['~', ['A']]], ['~', ['B']]]), justification='I∧',
                         on_steps=[0, 1], open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['∧', ['A'], ['~', ['A']]]), justification='E∧1', on_steps=[2],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=Formula(['~', ['~', ['B']]]), justification='I~', on_steps=[1, 3],
                         open_suppositions=[]),
    NaturalDeductionStep(content=Formula(['B']), justification='E~', on_steps=[4], open_suppositions=[]),
])
extra_derived_rules = {
    "repetition": repetition_derivation,
    "EFSQ": EFSQ_derivation,
}

classical_natural_deduction_solver2 = AltNaturalDeductionSolver(language=cl_language,
                                                        simplification_rules=standard_simplification_rules,
                                                        derived_rules_derivations=standard_derived_rules_derivations,
                                                        extra_derived_rules_derivations=extra_derived_rules,
                                                        heuristics=[efsq_heuristic,
                                                                    conjunction_heuristic,
                                                                    conditional_heuristic,
                                                                    disjunction_heuristic,
                                                                    reductio_heuristic])
