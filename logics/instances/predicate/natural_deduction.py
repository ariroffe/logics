from logics.classes.predicate import PredicateFormula as Formula
from logics.classes.predicate.proof_theories import (
    PredicateNaturalDeductionStep,
    PredicateNaturalDeductionRule,
    PredicateNaturalDeductionSystem,
)
from logics.instances.predicate.languages import classical_infinite_predicate_language

classical_primitive_rules = {

    'I~': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['⊥']), open_suppositions=[0]),
        PredicateNaturalDeductionStep(Formula(['~', ['A']]), 'I~', [0, 1], open_suppositions=[])
    ]),

    'E~': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['~', ['A']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['⊥']), 'E~', [0, 1], open_suppositions=[])
    ]),

    '~~': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['~', ['~', ['A']]]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), '~~', [0], open_suppositions=[])
    ]),

    'I→': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['B']), open_suppositions=[0]),
        PredicateNaturalDeductionStep(Formula(['→', ['A'], ['B']]), 'I→', [0, 1], open_suppositions=[])
    ]),

    'E→': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['→', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['B']), 'E→', [0, 1], open_suppositions=[])
    ]),

    'I∧': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['B']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∧', ['A'], ['B']]), 'I∧', [0, 1], open_suppositions=[])
    ]),

    'E∧1': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∧', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), 'E∧1', [0], open_suppositions=[])
    ]),

    'E∧2': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∧', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['B']), 'E∧2', [0], open_suppositions=[])
    ]),

    'I∨1': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∨', ['A'], ['B']]), 'I∨1', [0], open_suppositions=[])
    ]),

    'I∨2': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∨', ['B'], ['A']]), 'I∨2', [0], open_suppositions=[])
    ]),

    'E∨': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∨', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['→', ['A'], ['C']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['→', ['B'], ['C']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['C']), 'E∨', [0, 1, 2], open_suppositions=[])
    ]),

    'repetition': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), 'repetition', [0], open_suppositions=[])
    ]),

    'EFSQ': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['⊥']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['A']), 'EFSQ', [0], open_suppositions=[])
    ]),

    'E∀': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∀', 'χ', ['A']]), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['[α/χ]A']), 'I∨1', [0], open_suppositions=[])
    ]),

    'I∀': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['[α/χ]A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∀', 'χ', ['A']]), 'I∀', [0], open_suppositions=[])
    ], arbitrary_cts=['α']),

    'I∃': PredicateNaturalDeductionRule([
        '(...)',
        PredicateNaturalDeductionStep(Formula(['[α/χ]A']), open_suppositions=[]),
        '(...)',
        PredicateNaturalDeductionStep(Formula(['∃', 'χ', ['A']]), 'I∀', [0], open_suppositions=[])
    ]),
}

predicate_classical_natural_deduction_system = PredicateNaturalDeductionSystem(
    language=classical_infinite_predicate_language,
    rules=classical_primitive_rules
)
