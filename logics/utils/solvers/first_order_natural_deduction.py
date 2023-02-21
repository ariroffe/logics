from copy import copy, deepcopy

from logics.instances.predicate.languages import classical_predicate_language as cl_language
from logics.utils.solvers.natural_deduction import (
    NaturalDeductionSolver,
    standard_simplification_rules,
    standard_derived_rules_derivations,
    conjunction_heuristic,
    conditional_heuristic,
    disjunction_heuristic,
    Heuristic,
    ReductioHeuristic,
    EFSQHeuristic,
    SolverError
)
from logics.classes.predicate.proof_theories import Derivation
from logics.classes.predicate.proof_theories.natural_deduction import NaturalDeductionStep
from logics.classes.predicate import PredicateFormula, Inference
from logics.utils.etc.upgrade import upgrade_inference, upgrade_derivation

# ----------------------------------------------------------------------------
# ----------------------------------------------------------------------------
# First order classical ND solver

class FirstOrderNaturalDeductionSolver(NaturalDeductionSolver):
    def _get_formulae_to_add(self, rule_conclusion, subst_dict):
        if rule_conclusion.contains_string('[α/χ]A'):
            # Here just add every possible instance (this is mainly for instantiating E∀)
            new_subst_dict = copy(subst_dict)
            formulae_to_add = list()
            for ind_ct in self.language.individual_constants:
                new_subst_dict['α'] = ind_ct
                formulae_to_add.append(rule_conclusion.instantiate(self.language, new_subst_dict))
            return formulae_to_add
        return super()._get_formulae_to_add(rule_conclusion, subst_dict)

    @staticmethod
    def get_arbitrary_constant(language, derivation):
        """Given a derivation, returns an individual constant that is arbitrary up to the last step

        For now, returns something completely new to the derivation (easier)"""
        possible_ind_constants = copy(language.individual_constants)
        for step in derivation:
            for ind_constant in reversed(possible_ind_constants):  # loop it in reverse bc we are changing the bound
                if step.content.contains_string(ind_constant):
                    possible_ind_constants.remove(ind_constant)
        if not possible_ind_constants:
            return None
        return possible_ind_constants[0]

    def _get_non_premise_replacement(self, hardcoded_derivation_step, subst_dict, derivation):
        # Simply add an abritrary ind constant as an instance of α and then call the super method
        if hardcoded_derivation_step.contains_string('[α/χ]A'):
            if 'α' not in subst_dict:
                arbitrary_ct = self.get_arbitrary_constant(self.language, derivation)
                if arbitrary_ct is None:
                    raise SolverError(f'Could not find arbitrary constant for step {len(derivation)}')
                subst_dict['α'] = arbitrary_ct
        return super()._get_non_premise_replacement(hardcoded_derivation_step, subst_dict, derivation)

# ----------------------------------------------------------------------------
# New simplification rules and their hardcoded derivations

first_order_simplification_rules = deepcopy(standard_simplification_rules)
first_order_derived_rules_derivations = deepcopy(standard_derived_rules_derivations)
# We need to turn Formula into PredicateFormula for this solver
for rule_name in first_order_simplification_rules:
    rule = first_order_simplification_rules[rule_name]
    first_order_simplification_rules[rule_name] = upgrade_inference(rule)
for derivation_name in first_order_derived_rules_derivations:
    derivation = first_order_derived_rules_derivations[derivation_name]
    first_order_derived_rules_derivations[derivation_name] = upgrade_derivation(derivation)


first_order_simplification_rules["E∀"] = Inference(premises=[PredicateFormula(['∀', 'χ', ['A']])],
                                                   conclusions=[PredicateFormula(['[α/χ]A'])])
first_order_simplification_rules["NegUniv"] = Inference(premises=[PredicateFormula(['~', ['∀', 'χ', ['A']]])],
                                                     conclusions=[PredicateFormula(['∃', 'χ', ['~', ['A']]])])
first_order_simplification_rules["NegExist"] = Inference(premises=[PredicateFormula(['~', ['∃', 'χ', ['A']]])],
                                                     conclusions=[PredicateFormula(['∀', 'χ', ['~', ['A']]])])

NegUniv_derivation = Derivation([
    NaturalDeductionStep(content=PredicateFormula(['~', ['∀', 'χ', ['A']]]), justification='premise',
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['~', ['∃', 'χ', ['~', ['A']]]]), justification='supposition',
                         open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['~', ['[α/χ]A']]), justification='supposition',
                         open_suppositions=[1, 2]),
    #3
    NaturalDeductionStep(content=PredicateFormula(['∃', 'χ', ['~', ['A']]]), justification='I∃', on_steps=[2],
                         open_suppositions=[1, 2]),
    NaturalDeductionStep(content=PredicateFormula(['⊥']), justification='E~', on_steps=[1, 3], open_suppositions=[1,2]),
    #5
    NaturalDeductionStep(content=PredicateFormula(['~', ['~', ['[α/χ]A']]]), justification='I~', on_steps=[2, 4],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['[α/χ]A']), justification='DN', on_steps=[5], open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['∀', 'χ', ['A']]), justification='I∀', on_steps=[6],
                         open_suppositions=[1]),
    #8
    NaturalDeductionStep(content=PredicateFormula(['⊥']), justification='E~', on_steps=[1, 3], open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['~', ['~', ['∃', 'χ', ['~', ['A']]]]]), justification='I~',
                         on_steps=[1, 8], open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['∃', 'χ', ['~', ['A']]]), justification='DN', on_steps=[9],
                         open_suppositions=[]),
])
NegExist_derivation = Derivation([
    NaturalDeductionStep(content=PredicateFormula(['~', ['∃', 'χ', ['A']]]), justification='premise',
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['[α/χ]A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['∃', 'χ', ['A']]), justification='I∃', on_steps=[1],
                         open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['⊥']), justification='E~', on_steps=[0, 2], open_suppositions=[1]),
    #4
    NaturalDeductionStep(content=PredicateFormula(['~', ['[α/χ]A']]), justification='I~', on_steps=[1, 3],
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['∀', 'χ', ['~', ['A']]]), justification='I∀', on_steps=[4],
                         open_suppositions=[])
])
first_order_derived_rules_derivations["NegUniv"] = NegUniv_derivation
first_order_derived_rules_derivations["NegExist"] = NegExist_derivation

# ----------------------------------------------------------------------------
# New heuristics

predicate_EFSQ_heuristic = EFSQHeuristic(formula_class=PredicateFormula)
predicate_reductio_heuristic = ReductioHeuristic(formula_class=PredicateFormula)


class ExistentialEliminationHeuristic(Heuristic):
    def __init__(self, language):
        self.language = language

    def get_first_untried_existential_idx(self, derivation, tried_existentials):
        open_sups = FirstOrderNaturalDeductionSolver._get_current_open_sups(derivation)
        for step_idx in range(len(derivation)):
            # get the step number of the first existential formula that is not in tried_existentials and that
            # is not in a closed supposition
            step = derivation[step_idx]
            if step_idx not in tried_existentials and step.content[0] == "∃" and \
                    not FirstOrderNaturalDeductionSolver._is_in_closed_supposition(step.open_suppositions, open_sups):
                return step_idx
        return None

    def is_applicable(self, goal):
        return True  # we need to check if applicable below anyway, so let's not repeat the check here

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        # Get the first untried existential
        existential_idx = self.get_first_untried_existential_idx(derivation, tried_existentials)
        if existential_idx is None:
            raise SolverError("No existentials left to try")
        tried_existentials.append(existential_idx)  # Add it so that we don't try it again
        existential = derivation[existential_idx].content

        deriv1 = deepcopy(derivation)

        # Get an arbitrary individual constant
        # Need to check that the constant is not in the consequent as well, so lets add it at the end and then remove it
        deriv1.append(NaturalDeductionStep(content=goal, justification='premise'))
        arbitrary_ct = FirstOrderNaturalDeductionSolver.get_arbitrary_constant(self.language, deriv1)
        if arbitrary_ct is None:
            raise SolverError('Could not find an arbtitrary constant to work with the existential heuristic')
        del deriv1[-1]

        # Add an instance of the existential as a supposition
        supposition = existential[2].vsubstitute(existential[1], arbitrary_ct)

        prev_open_sups = solver._get_current_open_sups(derivation)
        sup_step = len(derivation)
        new_open_sups = prev_open_sups + [sup_step]
        deriv1.append(NaturalDeductionStep(content=supposition, justification='supposition',
                                           on_steps=[], open_suppositions=new_open_sups))

        # Solve for the goal of the original derivation
        deriv1 = solver._solve_derivation(derivation=deriv1, goal=goal, tried_existentials=tried_existentials)

        # If deriv1 has one more step (the supposition), it is because the derivation already contained the goal (this
        # should not happen but just in case) and therefore it just returned. We need to repeat the goal to close it.
        goal_step = solver._get_step_of_formula(goal, deriv1, new_open_sups)
        if len(deriv1) == len(derivation)+1:
            deriv1.append(NaturalDeductionStep(content=goal[2], justification='repetition',
                                               on_steps=[goal_step],
                                               open_suppositions=copy(new_open_sups)))
        # Now add the conditional and the existential elimination
        deriv1.append(NaturalDeductionStep(content=PredicateFormula(['→', supposition, goal]), justification="I→",
                                           on_steps=[sup_step, goal_step], open_suppositions=copy(prev_open_sups)))
        deriv1.append(NaturalDeductionStep(content=goal, justification="E∃",
                                           on_steps=[existential_idx, len(deriv1)-1],
                                           open_suppositions=copy(prev_open_sups)))
        return deriv1


existential_elim_heuristic = ExistentialEliminationHeuristic(language=cl_language)


class ExistentialIntroductionHeuristic(Heuristic):
    rule_justification = 'I∃'

    def __init__(self, language):
        self.language = language

    def is_applicable(self, goal):
        return goal.main_symbol == '∃'

    def _is_arbitrary_constant(self, ind_ct, formula_quantified, derivation):
        return True  # Here we don't care about this, just return true. Will be overloaded in the UnivIntroHeuristic

    def apply_heuristic(self, derivation, goal, solver, tried_existentials):
        # Basically, try to derive every possible substitution instance
        deriv1 = deepcopy(derivation)
        prev_open_sups = solver._get_current_open_sups(derivation)

        # Try to solve for each disjunct separately
        for ind_ct in self.language.individual_constants:
            # Get the free variables in the formula quantified
            free_vars = tuple(goal[2].free_variables(self.language))
            if not free_vars:
                subst_instance = goal[2]  # There are none, the formula is just the formula quantified
            else:
                # For the universal intro heuristic below. Has to be here bc if no free vars, we don't care about ind_ct
                if not self._is_arbitrary_constant(ind_ct, goal[2], derivation):
                    continue
                subst_instance = goal[2].vsubstitute(free_vars[0], ind_ct)

            try:
                deriv1 = solver._solve_derivation(derivation=deriv1, goal=subst_instance)

                # Look for where the instance is (may not be the last step if it was present in the derivation?)
                step_num = solver._get_step_of_formula(subst_instance, deriv1, prev_open_sups)
                deriv1.append(NaturalDeductionStep(content=goal, justification=self.rule_justification,
                                                   on_steps=[step_num],
                                                   open_suppositions=copy(prev_open_sups)))
                return deriv1
            except SolverError:
                if not free_vars:
                    break  # if there are no free variables every subst instance will be the same, so just break here

        # After trying all possible subst instances, exit
        raise SolverError("Could not derive substitution instance")


existential_intro_heuristic = ExistentialIntroductionHeuristic(language=cl_language)


class UniversalIntroductionHeuristic(ExistentialIntroductionHeuristic):
    rule_justification = 'I∀'

    def is_applicable(self, goal):
        return goal.main_symbol == '∀'

    def _is_arbitrary_constant(self, ind_ct, formula_quantified, derivation):
        # Check that the ind ct is not in the formula quantified
        if formula_quantified.contains_string(ind_ct):
            return False
        for step_idx in range(len(derivation)):
            step = derivation[step_idx]
            # Check that the ind ct is not in a premise
            if step.justification == 'premise' and step.content.contains_string(ind_ct):
                return False
            # Check that it is not in an open supposition
            if step.justification == 'supposition' and step.content.contains_string(ind_ct) and \
                    step_idx in derivation[-1].open_suppositions:
                return False
        return True

universal_intro_heuristic = UniversalIntroductionHeuristic(language=cl_language)


# ----------------------------------------------------------------------------
# Solver instance

first_order_natural_deduction_solver = FirstOrderNaturalDeductionSolver(language=cl_language,
                                                        simplification_rules=first_order_simplification_rules,
                                                        derived_rules_derivations=first_order_derived_rules_derivations,
                                                        heuristics=[existential_elim_heuristic,
                                                                    predicate_EFSQ_heuristic,
                                                                    conjunction_heuristic,
                                                                    conditional_heuristic,
                                                                    disjunction_heuristic,
                                                                    existential_intro_heuristic,
                                                                    universal_intro_heuristic,
                                                                    predicate_reductio_heuristic])
