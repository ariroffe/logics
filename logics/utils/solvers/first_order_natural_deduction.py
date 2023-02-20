from copy import copy, deepcopy

from logics.instances.predicate.languages import classical_predicate_language as cl_language
from logics.utils.solvers.natural_deduction import (
    NaturalDeductionSolver,
    standard_simplification_rules,
    standard_derived_rules_derivations,
    efsq_heuristic,
    conjunction_heuristic,
    conditional_heuristic,
    disjunction_heuristic,
    reductio_heuristic,
    SolverError
)
from logics.classes.predicate.proof_theories import Derivation
from logics.classes.predicate.proof_theories.natural_deduction import NaturalDeductionStep
from logics.classes.predicate import PredicateFormula, Inference
from logics.utils.etc.upgrade import upgrade_inference, upgrade_derivation

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

    def get_arbitrary_constant(self, derivation):
        """Given a derivation, returns an individual constant that is arbitrary up to the last step

        For now, returns something completely new to the derivation (easier)"""
        possible_ind_constants = copy(self.language.individual_constants)
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
                arbitrary_ct = self.get_arbitrary_constant(derivation)
                if arbitrary_ct is None:
                    raise SolverError(f'Could not find arbitrary constant for step {len(derivation)}')
                subst_dict['α'] = arbitrary_ct
        return super()._get_non_premise_replacement(hardcoded_derivation_step, subst_dict, derivation)


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

first_order_natural_deduction_solver = FirstOrderNaturalDeductionSolver(language=cl_language,
                                                        simplification_rules=first_order_simplification_rules,
                                                        derived_rules_derivations=first_order_derived_rules_derivations,
                                                        heuristics=[efsq_heuristic,
                                                                    conjunction_heuristic,
                                                                    conditional_heuristic,
                                                                    disjunction_heuristic,
                                                                    reductio_heuristic])
