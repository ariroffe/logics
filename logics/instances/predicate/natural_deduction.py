from copy import deepcopy

from logics.classes.predicate import PredicateFormula
from logics.classes.predicate.proof_theories import (
    NaturalDeductionStep,
    PredicateNaturalDeductionRule,
    PredicateNaturalDeductionSystem,
)
from logics.instances.predicate.languages import classical_infinite_predicate_language
from logics.instances.propositional.natural_deduction import classical_primitive_rules
from logics.utils.upgrade import upgrade_derivation


first_order_primitive_rules = deepcopy(classical_primitive_rules)

# Turn Formulae into PredicateFormulae, NaturalDeductionRule into PredicateNaturalDeductionRule
for rule_name in first_order_primitive_rules:
    first_order_primitive_rules[rule_name] = upgrade_derivation(first_order_primitive_rules[rule_name])

# Add the remaining rules
first_order_primitive_rules.update({
    'E∀': PredicateNaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(PredicateFormula(['∀', 'χ', ['A']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(PredicateFormula(['[α/χ]A']), 'E∀', [0], open_suppositions=[])
    ]),

    'I∀': PredicateNaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(PredicateFormula(['[α/χ]A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(PredicateFormula(['∀', 'χ', ['A']]), 'I∀', [0], open_suppositions=[])
    ], arbitrary_cts=['α']),

    'I∃': PredicateNaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(PredicateFormula(['[α/χ]A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(PredicateFormula(['∃', 'χ', ['A']]), 'I∃', [0], open_suppositions=[])
    ]),

    'E∃': PredicateNaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(PredicateFormula(['∃', 'χ', ['A']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(PredicateFormula(['→', ['[α/χ]A'], ['B']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(PredicateFormula(['B']), 'E∃', [0, 1], open_suppositions=[]),
    ], arbitrary_cts=['α']),
})

predicate_classical_natural_deduction_system = PredicateNaturalDeductionSystem(
    language=classical_infinite_predicate_language,
    rules=first_order_primitive_rules,
)
