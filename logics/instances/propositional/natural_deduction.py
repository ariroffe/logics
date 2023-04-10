from copy import deepcopy
from itertools import permutations

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
        NaturalDeductionStep(Formula(['~', ['A']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['⊥']), 'E~', [0, 1], open_suppositions=[])
    ]),

    '~~': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['~', ['~', ['A']]]), open_suppositions=[]),
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
        NaturalDeductionStep(Formula(['→', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['B']), 'E→', [0, 1], open_suppositions=[])
    ]),

    'I∧': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['B']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), 'I∧', [0, 1], open_suppositions=[])
    ]),

    'E∧1': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'E∧1', [0], open_suppositions=[])
    ]),

    'E∧2': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['B']), 'E∧2', [0], open_suppositions=[])
    ]),

    'I∨1': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['A'], ['B']]), 'I∨1', [0], open_suppositions=[])
    ]),

    'I∨2': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['B'], ['A']]), 'I∨2', [0], open_suppositions=[])
    ]),

    'E∨': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['∨', ['A'], ['B']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['→', ['A'], ['C']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['→', ['B'], ['C']]), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['C']), 'E∨', [0, 1, 2], open_suppositions=[])
    ]),

    'repetition': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['A']), open_suppositions=[]),
        '(...)',
        NaturalDeductionStep(Formula(['A']), 'repetition', [0], open_suppositions=[])
    ]),

    'EFSQ': NaturalDeductionRule([
        '(...)',
        NaturalDeductionStep(Formula(['⊥']), open_suppositions=[]),
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
    NaturalDeductionStep(Formula(['~', ['~', ['A']]]), open_suppositions=[]),
    '(...)',
    NaturalDeductionStep(Formula(['A']), 'E~', [0], open_suppositions=[])
])
# The following are taken as derived rules
del classical_natural_deduction_system2.rules['~~']
del classical_natural_deduction_system2.rules['repetition']
del classical_natural_deduction_system2.rules['EFSQ']


# ------------------------------------------------------------
# Versions with reversible rules (no need to put the 'on steps' in a specific order)
# Takes advantage of the fact that you can add a numeral at the end

unordered_rules = deepcopy(classical_primitive_rules)

# Negation elimination
neg_elim = unordered_rules.pop('E~')
unordered_rules['E~1'] = deepcopy(neg_elim)
unordered_rules['E~1'][-1] = NaturalDeductionStep(Formula(['⊥']), 'E~1', [0, 1], open_suppositions=[])
unordered_rules['E~2'] = deepcopy(neg_elim)
unordered_rules['E~2'][-1] = NaturalDeductionStep(Formula(['⊥']), 'E~2', [1, 0], open_suppositions=[])

cond_elim = unordered_rules.pop('E→')
unordered_rules['E→1'] = deepcopy(cond_elim)
unordered_rules['E→1'][-1] = NaturalDeductionStep(Formula(['B']), 'E→1', [0, 1], open_suppositions=[])
unordered_rules['E→2'] = deepcopy(cond_elim)
unordered_rules['E→2'][-1] = NaturalDeductionStep(Formula(['B']), 'E→2', [1, 0], open_suppositions=[])

conj_intro = unordered_rules.pop('I∧')
unordered_rules['I∧1'] = deepcopy(conj_intro)
unordered_rules['I∧1'][-1] = NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), 'I∧1', [0, 1], open_suppositions=[])
unordered_rules['I∧2'] = deepcopy(conj_intro)
unordered_rules['I∧2'][-1] = NaturalDeductionStep(Formula(['∧', ['A'], ['B']]), 'I∧2', [1, 0], open_suppositions=[])

# This one has more permutations available for the on_steps
disj_elim = unordered_rules.pop('E∨')
count = 1
for perm in permutations([0, 1, 2]):
    unordered_rules[f'E∨{count}'] = deepcopy(disj_elim)
    unordered_rules[f'E∨{count}'][-1] = NaturalDeductionStep(Formula(['C']), f'E∨{count}', list(perm), open_suppositions=[])
    count += 1

classical_natural_deduction_system_unordered = NaturalDeductionSystem(
    language=classical_infinite_language_with_sent_constants,
    rules=unordered_rules,
)


# --------------------
# Same for system2

classical_natural_deduction_system2_unordered = deepcopy(classical_natural_deduction_system_unordered)

classical_natural_deduction_system2.rules['I~'] = NaturalDeductionRule([
    '(...)',
    NaturalDeductionStep(Formula(['A']), 'supposition', open_suppositions=[0]),
    '(...)',
    NaturalDeductionStep(Formula(['∧', ['B'], ['~', ['B']]]), open_suppositions=[0]),
    NaturalDeductionStep(Formula(['~', ['A']]), 'I~', [0, 1], open_suppositions=[])
])
classical_natural_deduction_system2.rules['E~'] = NaturalDeductionRule([
    '(...)',
    NaturalDeductionStep(Formula(['~', ['~', ['A']]]), open_suppositions=[]),
    '(...)',
    NaturalDeductionStep(Formula(['A']), 'E~', [0], open_suppositions=[])
])

del classical_natural_deduction_system2_unordered.rules['E~1']
del classical_natural_deduction_system2_unordered.rules['E~2']
del classical_natural_deduction_system2_unordered.rules['~~']
del classical_natural_deduction_system2_unordered.rules['repetition']
del classical_natural_deduction_system2_unordered.rules['EFSQ']
