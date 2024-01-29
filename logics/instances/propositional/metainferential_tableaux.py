from copy import deepcopy
from logics.instances.propositional.languages import classical_infinite_language
from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    MetainferentialTableauxStandard, MetainferentialTableauxNode, MetainferentialTableauxSystem
)
from logics.utils.solvers.tableaux import metainferential_tableaux_solver

# GENERAL RULES
# The following rules have no children because we apply them in a different, hardcoded, way
inf0 = MetainferentialTableauxNode(
    content=Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]),
    index=MetainferentialTableauxStandard(['X', 'Y'], bar=True),
)

inf1 = MetainferentialTableauxNode(
    content=Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]),
    index=MetainferentialTableauxStandard(['X', 'Y'], bar=False),
)

complement = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=True),
)

intersection = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=False),
)
MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('Y', bar=False),
    parent=intersection,
)

singleton = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=False),
)


metainferential_tableaux_rules = {
    'inf0': inf0,
    'inf1': inf1,
    'complement': complement,
    'intersection': intersection,
    'singleton': singleton,
}


# SK SCHEME
# ----------------------------------------------------------------------
S = MetainferentialTableauxStandard({'1'})
I = MetainferentialTableauxStandard({'i'})
F = MetainferentialTableauxStandard({'0'})
T = MetainferentialTableauxStandard({'1', 'i'})
N = MetainferentialTableauxStandard({'i', '0'})
D = MetainferentialTableauxStandard({'1', '0'})

SK_negation_1 = MetainferentialTableauxNode(content=Formula(['~', ['A']]), index=S)
MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R~1', parent=SK_negation_1)
'''
['~', ['A']], {'1'}
└── ['A'], {'0'} (R~1)
'''

SK_negation_i = MetainferentialTableauxNode(content=Formula(['~', ['A']]), index=I)
MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R~1', parent=SK_negation_i)
'''
['~', ['A']], {'i'}
└── ['A'], {'i'} (R~1)
'''

SK_negation_0 = MetainferentialTableauxNode(content=Formula(['~', ['A']]), index=F)
MetainferentialTableauxNode(content=Formula(['A']), index=S, justification='R~1', parent=SK_negation_0)
'''
['~', ['A']], {'0'}
└── ['A'], {'1'} (R~1)
'''

SK_conjunction_1 = MetainferentialTableauxNode(content=Formula(['∧', ['A'], ['B']]), index=S)
SKcj1 = MetainferentialTableauxNode(content=Formula(['A']), index=S, justification='R∧1', parent=SK_conjunction_1)
MetainferentialTableauxNode(content=Formula(['B']), index=S, justification='R∧1', parent=SKcj1)
'''
['∧', ['A'], ['B']], {'1'}
└── ['A'], {'1'} (R∧1)
    └── ['B'], {'1'} (R∧1)
'''

SK_conjunction_i = MetainferentialTableauxNode(content=Formula(['∧', ['A'], ['B']]), index=I)
SKcji_1 = MetainferentialTableauxNode(content=Formula(['A']), index=T, justification='R∧i', parent=SK_conjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R∧i', parent=SKcji_1)
SKcji_2 = MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R∧i', parent=SK_conjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=T, justification='R∧i', parent=SKcji_2)
'''
['∧', ['A'], ['B']], {'i'}
└── ['A'], {'1'} (R∧i)
    └── ['B'], {'1', 'i'} (R∧i)
└── ['A'], {'1', 'i'} (R∧i)
    └── ['B'], {'1'} (R∧i)
'''

SK_conjunction_0 = MetainferentialTableauxNode(content=Formula(['∧', ['A'], ['B']]), index=F)
MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R∧0', parent=SK_conjunction_0)
MetainferentialTableauxNode(content=Formula(['B']), index=F, justification='R∧0', parent=SK_conjunction_0)
'''
['∧', ['A'], ['B']], {'0'}
└── ['A'], {'0'} (R∧0)
└── ['B'], {'0'} (R∧0)
'''

SK_disjunction_1 = MetainferentialTableauxNode(content=Formula(['∨', ['A'], ['B']]), index=S)
MetainferentialTableauxNode(content=Formula(['A']), index=S, justification='R∨1', parent=SK_disjunction_1)
MetainferentialTableauxNode(content=Formula(['B']), index=S, justification='R∨1', parent=SK_disjunction_1)
'''
['∨', ['A'], ['B']], {'1'}
└── ['A'], {'1'} (R∨0)
└── ['B'], {'1'} (R∨0)
'''

SK_disjunction_i = MetainferentialTableauxNode(content=Formula(['∨', ['A'], ['B']]), index=I)
SKdji_1 = MetainferentialTableauxNode(content=Formula(['A']), index=N, justification='R∨i', parent=SK_disjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R∨i', parent=SKdji_1)
SKdji_2 = MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R∨i', parent=SK_disjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=N, justification='R∨i', parent=SKdji_2)
'''
['∨', ['A'], ['B']], {'i'}
└── ['A'], {'1', 'i'} (R∧i)
    └── ['B'], {'i'} (R∧i)
└── ['A'], {'i'} (R∧i)
    └── ['B'], {'1', 'i'} (R∧i)
'''

SK_disjunction_0 = MetainferentialTableauxNode(content=Formula(['∨', ['A'], ['B']]), index=F)
SKdj0 = MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R∨0', parent=SK_disjunction_0)
MetainferentialTableauxNode(content=Formula(['B']), index=F, justification='R∨0', parent=SKdj0)
'''
['∨', ['A'], ['B']], {'0'}
└── ['A'], {'0'} (R∨1)
    └── ['B'], {'0'} (R∨1)
'''

SK_conditional_1 = MetainferentialTableauxNode(content=Formula(['→', ['A'], ['B']]), index=S)
MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R→0', parent=SK_conditional_1)
MetainferentialTableauxNode(content=Formula(['B']), index=S, justification='R→0', parent=SK_conditional_1)
'''
['→', ['A'], ['B']], {'1'}
└── ['A'], {'0'} (R→1)
└── ['B'], {'1'} (R→1)
'''

SK_conditional_i = MetainferentialTableauxNode(content=Formula(['→', ['A'], ['B']]), index=I)
SKcdi_1 = MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R→i', parent=SK_conditional_i)
MetainferentialTableauxNode(content=Formula(['B']), index=N, justification='R→i', parent=SKcdi_1)
SKcdi_2 = MetainferentialTableauxNode(content=Formula(['A']), index=T, justification='R→i', parent=SK_conditional_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R→i', parent=SKcdi_2)
'''
['→', ['A'], ['B']], {'i'}
└── ['A'], {'i'} (R→i)
    └── ['B'], {'i'} (R→i)
└── ['A'], {'1', 'i'} (R→i)
    └── ['B'], {'i'} (R→i)
'''

SK_conditional_0 = MetainferentialTableauxNode(content=Formula(['→', ['A'], ['B']]), index=F)
SKcd0 = MetainferentialTableauxNode(content=Formula(['A']), index=S, justification='R→0', parent=SK_conditional_0)
MetainferentialTableauxNode(content=Formula(['B']), index=F, justification='R→0', parent=SKcd0)
'''
['→', ['A'], ['B']], {'0'}
└── ['A'], {'1'} (R→1)
    └── ['B'], {'0'} (R→1)
'''

SK_metainferential_tableaux_rules = deepcopy(metainferential_tableaux_rules)
SK_metainferential_tableaux_rules.update({
    'R~1': SK_negation_1,
    'R~i': SK_negation_i,
    'R~0': SK_negation_0,

    'R∧1': SK_conjunction_1,
    'R∧i': SK_conjunction_i,
    'R∧0': SK_conjunction_0,

    'R∨1': SK_disjunction_1,
    'R∨i': SK_disjunction_i,
    'R∨0': SK_disjunction_0,

    'R→1': SK_conditional_1,
    'R→i': SK_conditional_i,
    'R→0': SK_conditional_0,
})

SK_metainferential_tableaux_system = MetainferentialTableauxSystem(
    base_indexes={'1', 'i', '0'},
    language=classical_infinite_language,
    rules=SK_metainferential_tableaux_rules,
    closure_rules= [],  # we are using fast_node_is_closed so this is not necessary
    solver=metainferential_tableaux_solver,
)

# WK SCHEME
# ----------------------------------------------------------------------
WK_conjunction_i = MetainferentialTableauxNode(content=Formula(['∧', ['A'], ['B']]), index=I)
MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R∧i', parent=WK_conjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R∧i', parent=WK_conjunction_i)
'''
['∧', ['A'], ['B']], {'i'}
└── ['A'], {'i'} (R∧i)
└── ['B'], {'i'} (R∧i)
'''

WK_conjunction_0 = MetainferentialTableauxNode(content=Formula(['∧', ['A'], ['B']]), index=F)
WKcj0_1 = MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R∧0', parent=WK_conjunction_0)
MetainferentialTableauxNode(content=Formula(['B']), index=D, justification='R∧0', parent=WKcj0_1)
WKcj0_2 = MetainferentialTableauxNode(content=Formula(['B']), index=F, justification='R∧0', parent=WK_conjunction_0)
MetainferentialTableauxNode(content=Formula(['A']), index=D, justification='R∧0', parent=WKcj0_2)
'''
['∧', ['A'], ['B']], {'0'}
└── ['A'], {'0'} (R∧0)
    └── ['B'], {'1', '0'} (R∧0)
└── ['B'], {'0'} (R∧0)
    └── ['A'], {'1', '0'} (R∧0)
'''

WK_disjunction_i = MetainferentialTableauxNode(content=Formula(['∨', ['A'], ['B']]), index=I)
MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R∨i', parent=WK_disjunction_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R∨i', parent=WK_disjunction_i)
'''
['∨', ['A'], ['B']], {'i'}
└── ['A'], {'i'} (R∨i)
└── ['B'], {'i'} (R∨i)
'''

WK_disjunction_1 = MetainferentialTableauxNode(content=Formula(['∨', ['A'], ['B']]), index=S)
WKds1_1 = MetainferentialTableauxNode(content=Formula(['A']), index=S, justification='R∨1', parent=WK_disjunction_1)
MetainferentialTableauxNode(content=Formula(['B']), index=D, justification='R∨1', parent=WKds1_1)
WKds1_2 = MetainferentialTableauxNode(content=Formula(['B']), index=S, justification='R∨1', parent=WK_disjunction_1)
MetainferentialTableauxNode(content=Formula(['A']), index=D, justification='R∨1', parent=WKds1_2)
'''
['∨', ['A'], ['B']], {'1'}
└── ['A'], {'1'} (R∨1)
    └── ['B'], {'1', '0'} (R∨1)
└── ['B'], {'1'} (R∨1)
    └── ['A'], {'1', '0'} (R∨1)
'''

WK_conditional_i = MetainferentialTableauxNode(content=Formula(['→', ['A'], ['B']]), index=I)
MetainferentialTableauxNode(content=Formula(['A']), index=I, justification='R→i', parent=WK_conditional_i)
MetainferentialTableauxNode(content=Formula(['B']), index=I, justification='R→i', parent=WK_conditional_i)
'''
['→', ['A'], ['B']], {'i'}
└── ['A'], {'i'} (R→i)
└── ['B'], {'i'} (R→i)
'''

WK_conditional_1 = MetainferentialTableauxNode(content=Formula(['→', ['A'], ['B']]), index=S)
WKcd1_1 = MetainferentialTableauxNode(content=Formula(['A']), index=F, justification='R→1', parent=WK_conditional_1)
MetainferentialTableauxNode(content=Formula(['B']), index=D, justification='R→1', parent=WKcd1_1)
WKcd1_2 = MetainferentialTableauxNode(content=Formula(['B']), index=S, justification='R→1', parent=WK_conditional_1)
MetainferentialTableauxNode(content=Formula(['A']), index=D, justification='R→1', parent=WKcd1_2)
'''
['→', ['A'], ['B']], {'1'}
└── ['A'], {'1'} (R→1)
    └── ['B'], {'1', '0'} (R→1)
└── ['B'], {'1'} (R→1)
    └── ['A'], {'1', '0'} (R→1)
'''

WK_metainferential_tableaux_rules = deepcopy(SK_metainferential_tableaux_rules)
WK_metainferential_tableaux_rules.update({
    'R∧i': WK_conjunction_i,
    'R∧0': WK_conjunction_0,

    'R∨i': WK_disjunction_i,
    'R∨1': WK_disjunction_1,

    'R→i': WK_conditional_i,
    'R→1': WK_conditional_1,
})

WK_metainferential_tableaux_system = MetainferentialTableauxSystem(
    base_indexes={'1', 'i', '0'},
    language=classical_infinite_language,
    rules=WK_metainferential_tableaux_rules,
    closure_rules= [],  # we are using fast_node_is_closed so this is not necessary
    solver=metainferential_tableaux_solver,
)