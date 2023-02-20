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


class ExistentialHeuristic(Heuristic):
    def __init__(self, language):
        self.language = language

    def get_first_untried_existential_idx(self, derivation):
        return None

    def is_applicable(self, goal, derivation):
        # We need to see if there are any existentials that we have not tried to eliminate yet
        if self.get_first_untried_existential_idx(derivation) is not None:
            return True
        return False

    def apply_heuristic(self, derivation, goal, open_sups, jump_steps, solver):
        # Get the first untried existential
        existential_idx = self.get_first_untried_existential_idx(derivation)
        existential = derivation[existential_idx]
        existential_idx = solver._steps([existential_idx], jump_steps)[0]  # todo ver lo de jump_steps aca, es esto?

        # Get an arbitrary individual constant
        # Need to check that the constant is not in the consequent as well, so lets add it as premise at the end
        # to get the arbitrary ct and then remove it again
        derivation.append(NaturalDeductionStep(content=goal, justification='premise', on_steps=[], open_suppositions=[]))
        arbitrary_ct = FirstOrderNaturalDeductionSolver.get_arbitrary_constant(self.language, derivation)
        if arbitrary_ct is None:
            raise SolverError('Could not find an arbtitrary constant to work with the existential heuristic')
        del derivation[-1]

        # Add an instance of the existential as a supposition
        supposition = existential[2].vsubstitute(existential[1], arbitrary_ct)
        sup_intro_number = solver._steps([len(derivation)], jump_steps)[0]
        open_sups2 = open_sups + [sup_intro_number]
        derivation2 = copy(derivation)
        derivation2.append(NaturalDeductionStep(content=supposition, justification='supposition',
                                                on_steps=[], open_suppositions=copy(open_sups2)))
        prems = [step.content for step in derivation2]

        # Solve for the goal of the original derivation
        deriv = solver._solve_derivation(inference=Inference(prems, goal),
                                         open_sups=copy(open_sups2), jump_steps=jump_steps)

        # If deriv and derivation have the same number of steps, it is because the derivation already contained
        # the goal, and therefore it just returned. We need to repeat the consequent to close it.
        if len(deriv) == len(derivation2):
            consequent_step = next(index for index in range(len(derivation2)) if
                                   derivation2[index].content == goal[2])
            consequent_step = solver._steps([consequent_step], jump_steps)
            deriv.append(NaturalDeductionStep(content=goal, justification='repetition',
                                              on_steps=consequent_step,
                                              open_suppositions=copy(open_sups2)))

        # Now add the conditional and the existential elimination
        derivation2.extend([x for x in deriv if x.justification != 'premise'])
        conditional_step = solver._steps([len(derivation2) - 2], jump_steps)[0]
        derivation2.append(NaturalDeductionStep(content=PredicateFormula(['→', supposition, goal]), justification="I→",
                                                on_steps=[sup_intro_number,  # first number has jump calculated
                                                          conditional_step],
                                                open_suppositions=open_sups2[:-1]))
        derivation2.append(NaturalDeductionStep(content=goal, justification="E∃",
                                                on_steps=[existential_idx, sup_intro_number, conditional_step],
                                                open_suppositions=open_sups2[:-1]))
        return derivation2


existential_heuristic = ExistentialHeuristic(language=cl_language)


first_order_natural_deduction_solver = FirstOrderNaturalDeductionSolver(language=cl_language,
                                                        simplification_rules=first_order_simplification_rules,
                                                        derived_rules_derivations=first_order_derived_rules_derivations,
                                                        heuristics=[existential_heuristic,
                                                                    predicate_EFSQ_heuristic,
                                                                    conjunction_heuristic,
                                                                    conditional_heuristic,
                                                                    disjunction_heuristic,
                                                                    predicate_reductio_heuristic])
