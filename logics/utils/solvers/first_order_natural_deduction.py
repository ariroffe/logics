from copy import deepcopy

from logics.utils.solvers.natural_deduction import (
    NaturalDeductionSolver,
    standard_simplification_rules,
    standard_derived_rules_derivations
)
from logics.classes.predicate.proof_theories import Derivation
from logics.classes.predicate.proof_theories.natural_deduction import NaturalDeductionStep
from logics.classes.predicate import PredicateFormula, Inference
from logics.utils.etc.upgrade import upgrade_inference, upgrade_derivation

# ----------------------------------------------------------------------------
# First order classical ND solver

class FirstOrderNaturalDeductionSolver(NaturalDeductionSolver):
    pass


first_order_simplification_rules = deepcopy(standard_simplification_rules)
first_order_simplification_rules["E∀"] = Inference(premises=[PredicateFormula(['∀', 'χ', ['A']])],
                                                   conclusions=[PredicateFormula(['[α/χ]A'])])
first_order_simplification_rules["Neg∀"] = Inference(premises=[PredicateFormula(['~', ['∀', 'χ', ['A']]])],
                                                   conclusions=[PredicateFormula(['∃', 'χ', ['~', ['A']]])])
first_order_simplification_rules["Neg∃"] = Inference(premises=[PredicateFormula(['~', ['∃', 'χ', ['A']]])],
                                                   conclusions=[PredicateFormula(['∀', 'χ', ['~', ['A']]])])

first_order_derived_rules_derivations = deepcopy(standard_derived_rules_derivations)
NegUniv_derivation = Derivation([
    NaturalDeductionStep(content=PredicateFormula(['∨', ['A'], ['A']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['→', ['A'], ['A']]), justification='repetition', on_steps=[3],
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='E∨', on_steps=[0, 3, 4], open_suppositions=[]),
])
NegExist_derivation = Derivation([
    NaturalDeductionStep(content=PredicateFormula(['∨', ['A'], ['A']]), justification='premise', open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='supposition', open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='repetition', on_steps=[1], open_suppositions=[1]),
    NaturalDeductionStep(content=PredicateFormula(['→', ['A'], ['A']]), justification='I→', on_steps=[1, 2],
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['→', ['A'], ['A']]), justification='repetition', on_steps=[3],
                         open_suppositions=[]),
    NaturalDeductionStep(content=PredicateFormula(['A']), justification='E∨', on_steps=[0, 3, 4], open_suppositions=[]),
])

# We need to turn Formula into PredicateFormula for this solver
for rule_name in first_order_simplification_rules:
    rule = first_order_simplification_rules[rule_name]
    first_order_simplification_rules[rule_name] = upgrade_inference(rule)
for derivation_name in first_order_derived_rules_derivations:
    derivation = first_order_derived_rules_derivations[derivation_name]
    first_order_derived_rules_derivations[derivation_name] = upgrade_derivation(derivation)

