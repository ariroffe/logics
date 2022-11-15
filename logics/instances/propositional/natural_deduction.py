from copy import deepcopy

from logics.classes.propositional import Formula
from logics.classes.propositional.proof_theories import NaturalDeductionStep, NaturalDeductionRule, \
    NaturalDeductionSystem
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants

classical_primitive_rules = {

    'I~': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
        '(...)',
        NaturalDeductionStep(Formula(['⊥']), open_suppositions=[0]),
        NaturalDeductionStep(Formula(['~', ['A']]), 'I~', [0, 1], open_suppositions=[])
    ]),

    'E~': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['~', ['A']])),
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['⊥']), 'E~', [0, 1], open_suppositions=[])
    ]),

    '~~': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['~', ['~', ['A']]])),
        '(...)',
        NaturalDeductionStep(Formula(['A']), '~~', [0], open_suppositions=[])
    ]),

    'I→': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
        '(...)',
        NaturalDeductionStep(Formula(['B']), open_suppositions=[0]),
        NaturalDeductionStep(Formula(['→', ['A'], ['B']]), 'I→', [0, 1], open_suppositions=[])
    ]),

    'E→': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['→', ['A'], ['B']])),
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['B']), 'E→', [0, 1], open_suppositions=[])
    ]),

    'I∧': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['B'])),
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), 'I∧', [0, 1], open_suppositions=[])
    ]),

    'E∧1': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']])),
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'E∧1', [0], open_suppositions=[])
    ]),

    'E∧2': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']])),
        '(...)',
        NaturalDeductionStep(Formula(['B']), 'E∧2', [0], open_suppositions=[])
    ]),

    'I∨1': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['A'], ['B']]), 'I∨1', [0], open_suppositions=[])
    ]),

    'I∨2': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['B'], ['A']]), 'I∨2', [0], open_suppositions=[])
    ]),

    'E∨': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['A'], ['B']])),
        '(...)',
        NaturalDeductionStep(Formula(['→', ['A'], ['C']])),
        '(...)',
        NaturalDeductionStep(Formula(['→', ['B'], ['C']])),
        '(...)',
        NaturalDeductionStep(Formula(['C']), 'E∨', [0, 1, 2], open_suppositions=[])
    ]),

    'repetition': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A'])),
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'repetition', [0], open_suppositions=[])
    ]),

    'EFSQ': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['⊥'])),
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'EFSQ', [0], open_suppositions=[])
    ]),

}

classical_natural_deduction_system = NaturalDeductionSystem(language=classical_infinite_language_with_sent_constants,
                                                            rules=classical_primitive_rules)

# ------------------------------------------------------------
# Another usual presentation of the classical ND system (E~ is double negation), no repetition and EFSQ as primitives
classical_natural_deduction_system2 = deepcopy(classical_natural_deduction_system)
# Negation introduction is with the conjunction instead of Falsum
classical_natural_deduction_system2.rules['I~'] = NaturalDeductionRule([
    '(...)',
    NaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
    '(...)',
    NaturalDeductionStep(Formula(['∧', ['B'], ['~', ['B']]]), open_suppositions=[0]),
    NaturalDeductionStep(Formula(['~', ['A']]), 'I~', [0, 1], open_suppositions=[])
])
# Negation elimination is double negation
classical_natural_deduction_system2.rules['E~'] = NaturalDeductionRule([
    '(...)',
    NaturalDeductionStep(Formula(['~', ['~', ['A']]])),
    '(...)',
    NaturalDeductionStep(Formula(['A']), 'E~', [0], open_suppositions=[])
])
# The following are taken as derived rules
del classical_natural_deduction_system2.rules['~~']
del classical_natural_deduction_system2.rules['repetition']
del classical_natural_deduction_system2.rules['EFSQ']
