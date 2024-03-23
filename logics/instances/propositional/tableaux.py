from logics.classes.propositional import Formula
from logics.instances.propositional.languages import classical_infinite_language
from logics.classes.propositional.proof_theories.tableaux import TableauxNode, TableauxSystem, IndexedTableauxSystem, \
    ManyValuedTableauxSystem, ConstructiveTreeSystem
from logics.utils.solvers.tableaux import standard_tableaux_solver, indexed_tableaux_solver, constructive_tree_solver
from logics.instances.propositional.languages import classical_infinite_language_noconditional


# ----------------------------------------------------------------------------------------------------------------------
# TABLEAUX FOR CLASSICAL LOGIC (e.g., Priest 2008)

classical_double_negation_rule = TableauxNode(content=Formula(['~', ['~', ['A']]]))
TableauxNode(content=Formula(['A']), justification='R~~', parent=classical_double_negation_rule)
'''
['~', ['~', ['A']]]
└── ['A'] (R~~)
'''

classical_conjunction_rule = TableauxNode(content=Formula(['∧', ['A'], ['B']]))
ccr2 = TableauxNode(content=Formula(['A']), justification='R∧', parent=classical_conjunction_rule)
TableauxNode(content=Formula(['B']), justification='R∧', parent=ccr2)
'''
['∧', ['A'], ['B']]
└── ['A'] (R∧)
    └── ['B'] (R∧)
'''

classical_neg_conjunction_rule = TableauxNode(content=Formula(['~', ['∧', ['A'], ['B']]]))
TableauxNode(content=Formula(['~', ['A']]), justification='R~∧', parent=classical_neg_conjunction_rule)
TableauxNode(content=Formula(['~', ['B']]), justification='R~∧', parent=classical_neg_conjunction_rule)
'''
['~', ['∧', ['A'], ['B']]]
├── ['~', ['A']] (R~∧)
└── ['~', ['B']] (R~∧)
'''

classical_disjunction_rule = TableauxNode(content=Formula(['∨', ['A'], ['B']]))
TableauxNode(content=Formula(['A']), justification='R∨', parent=classical_disjunction_rule)
TableauxNode(content=Formula(['B']), justification='R∨', parent=classical_disjunction_rule)
'''
['∨', ['A'], ['B']]
├── ['A'] (R∨)
└── ['B'] (R∨)
'''

classical_neg_disjunction_rule = TableauxNode(content=Formula(['~', ['∨', ['A'], ['B']]]))
cndr2 = TableauxNode(content=Formula(['~', ['A']]), justification='R~∨', parent=classical_neg_disjunction_rule)
TableauxNode(content=Formula(['~', ['B']]), justification='R~∨', parent=cndr2)
'''
['~', ['∨', ['A'], ['B']]]
└── ['~', ['A']] (R~∨)
    └── ['~', ['B']] (R~∨)
'''

classical_conditional_rule = TableauxNode(content=Formula(['→', ['A'], ['B']]))
TableauxNode(content=Formula(['~', ['A']]), justification='R→', parent=classical_conditional_rule)
TableauxNode(content=Formula(['B']), justification='R→', parent=classical_conditional_rule)
'''
['→', ['A'], ['B']]
├── ['~', ['A']] (R→)
└── ['B'] (R→)
'''

classical_neg_conditional_rule = TableauxNode(content=Formula(['~', ['→', ['A'], ['B']]]))
cncr2 = TableauxNode(content=Formula(['A']), justification='R~→', parent=classical_neg_conditional_rule)
TableauxNode(content=Formula(['~', ['B']]), justification='R~→', parent=cncr2)
'''
['~', ['→', ['A'], ['B']]]
└── ['A'] (R~→)
    └── ['~', ['B']] (R~→)
'''

classical_biconditional_rule = TableauxNode(content=Formula(['↔', ['A'], ['B']]))
cbr2 = TableauxNode(content=Formula(['A']), justification='R↔', parent=classical_biconditional_rule)
TableauxNode(content=Formula(['B']), justification='R↔', parent=cbr2)
cbr3 = TableauxNode(content=Formula(['~', ['A']]), justification='R↔', parent=classical_biconditional_rule)
TableauxNode(content=Formula(['~', ['B']]), justification='R↔', parent=cbr3)
'''
['↔', ['A'], ['B']]
├── ['A'] (R↔)
│   └── ['B'] (R↔)
└── ['~', ['A']] (R↔)
    └── ['~', ['B']] (R↔)
'''

classical_neg_biconditional_rule = TableauxNode(content=Formula(['~', ['↔', ['A'], ['B']]]))
cnbr2 = TableauxNode(content=Formula(['~', ['A']]), justification='R~↔', parent=classical_neg_biconditional_rule)
TableauxNode(content=Formula(['B']), justification='R~↔', parent=cnbr2)
cnbr3 = TableauxNode(content=Formula(['A']), justification='R~↔', parent=classical_neg_biconditional_rule)
TableauxNode(content=Formula(['~', ['B']]), justification='R~↔', parent=cnbr3)
'''
['~', ['↔', ['A'], ['B']]]
├── ['~', ['A']] (R~↔)
│   └── ['B'] (R~↔)
└── ['A'] (R~↔)
    └── ['~', ['B']] (R~↔)
'''

classical_tableaux_rules = {
    'R~~': classical_double_negation_rule,
    'R∧': classical_conjunction_rule,
    'R~∧': classical_neg_conjunction_rule,
    'R∨': classical_disjunction_rule,
    'R~∨': classical_neg_disjunction_rule,
    'R→': classical_conditional_rule,
    'R~→': classical_neg_conditional_rule,
    'R↔': classical_biconditional_rule,
    'R~↔': classical_neg_biconditional_rule,
}

classical_closure_rules = [
    [TableauxNode(content=Formula(['~', ['A']])), TableauxNode(content=Formula(['A']))]
]

classical_tableaux_system = TableauxSystem(language=classical_infinite_language,
                                           rules=classical_tableaux_rules,
                                           closure_rules= classical_closure_rules,
                                           solver=standard_tableaux_solver)


# ----------------------------------------------------------------------------------------------------------------------
# INDEXED PRESENTATION OF CLASSICAL TABLEAUX (e.g., Open Logic Project)

idx_classical_negation1 = TableauxNode(content=Formula(['~', ['A']]), index=1)
TableauxNode(content=Formula(['A']), index=0, justification='R~1', parent=idx_classical_negation1)
'''
['~', ['A']], 1
└── ['A'], 0 (R~1)
'''

idx_classical_negation0 = TableauxNode(content=Formula(['~', ['A']]), index=0)
TableauxNode(content=Formula(['A']), index=1, justification='R~0', parent=idx_classical_negation0)
'''
['~', ['A']], 0
└── ['A'], 1 (R~0)
'''

idx_classical_conjunction1 = TableauxNode(content=Formula(['∧', ['A'], ['B']]), index=1)
idx_cr2 = TableauxNode(content=Formula(['A']), index=1, justification='R∧1', parent=idx_classical_conjunction1)
TableauxNode(content=Formula(['B']), index=1, justification='R∧1', parent=idx_cr2)
'''
['∧', ['A'], ['B']], 1
└── ['A'], 1 (R∧1)
    └── ['B'], 1 (R∧1)
'''

idx_classical_conjunction0 = TableauxNode(content=Formula(['∧', ['A'], ['B']]), index=0)
TableauxNode(content=Formula(['A']), index=0, justification='R∧0', parent=idx_classical_conjunction0)
TableauxNode(content=Formula(['B']), index=0, justification='R∧0', parent=idx_classical_conjunction0)
'''
['∧', ['A'], ['B']], 0
├── ['A'], 0 (R∧0)
└── ['B'], 0 (R∧0)
'''

idx_classical_disjunction1 = TableauxNode(content=Formula(['∨', ['A'], ['B']]), index=1)
TableauxNode(content=Formula(['A']), index=1, justification='R∨1', parent=idx_classical_disjunction1)
TableauxNode(content=Formula(['B']), index=1, justification='R∨1', parent=idx_classical_disjunction1)
'''
['∨', ['A'], ['B']], 1
├── ['A'], 1 (R∨1)
└── ['B'], 1 (R∨1)
'''

idx_classical_disjunction0 = TableauxNode(content=Formula(['∨', ['A'], ['B']]), index=0)
idx_dr2 = TableauxNode(content=Formula(['A']), index=0, justification='R∨0', parent=idx_classical_disjunction0)
TableauxNode(content=Formula(['B']), index=0, justification='R∨0', parent=idx_dr2)
'''
['∨', ['A'], ['B']], 0
└── ['A'], 0 (R∨0)
    └── ['B'], 0 (R∨0)
'''

idx_classical_conditional1 = TableauxNode(content=Formula(['→', ['A'], ['B']]), index=1)
TableauxNode(content=Formula(['A']), index=0, justification='R→1', parent=idx_classical_conditional1)
TableauxNode(content=Formula(['B']), index=1, justification='R→1', parent=idx_classical_conditional1)
'''
['→', ['A'], ['B']], 1
├── ['A'], 0 (R→1)
└── ['B'], 1 (R→1)
'''

idx_classical_conditional0 = TableauxNode(content=Formula(['→', ['A'], ['B']]), index=0)
idx_cr2 = TableauxNode(content=Formula(['A']), index=1, justification='R→0', parent=idx_classical_conditional0)
TableauxNode(content=Formula(['B']), index=0, justification='R→0', parent=idx_cr2)
'''
['→', ['A'], ['B']], 0
└── ['A'], 1 (R→0)
    └── ['B'], 0 (R→0)
'''

idx_classical_biconditional1 = TableauxNode(content=Formula(['↔', ['A'], ['B']]), index=1)
idx_cbr2 = TableauxNode(content=Formula(['A']), index=1, justification='R↔1', parent=idx_classical_biconditional1)
TableauxNode(content=Formula(['B']), index=1, justification='R↔1', parent=idx_cbr2)
idx_cbr3 = TableauxNode(content=Formula(['A']), index=0, justification='R↔1', parent=idx_classical_biconditional1)
TableauxNode(content=Formula(['B']), index=0, justification='R↔1', parent=idx_cbr3)
'''
['↔', ['A'], ['B']], 1
├── ['A'], 1 (R↔1)
│   └── ['B'], 1 (R↔1)
└── ['A'], 0 (R↔1)
    └── ['B'], 0 (R↔1)
'''

idx_classical_biconditional0 = TableauxNode(content=Formula(['↔', ['A'], ['B']]), index=0)
idx_cbr4 = TableauxNode(content=Formula(['A']), index=1, justification='R↔0', parent=idx_classical_biconditional0)
TableauxNode(content=Formula(['B']), index=0, justification='R↔0', parent=idx_cbr4)
idx_cbr5 = TableauxNode(content=Formula(['A']), index=0, justification='R↔0', parent=idx_classical_biconditional0)
TableauxNode(content=Formula(['B']), index=1, justification='R↔0', parent=idx_cbr5)
'''
['↔', ['A'], ['B']], 0
├── ['A'], 1 (R↔0)
│   └── ['B'], 0 (R↔0)
└── ['A'], 0 (R↔0)
    └── ['B'], 1 (R↔0)
'''

idx_classical_tableaux_rules = {
    'R~1': idx_classical_negation1,
    'R~0': idx_classical_negation0,
    'R∧1': idx_classical_conjunction1,
    'R∧0': idx_classical_conjunction0,
    'R∨1': idx_classical_disjunction1,
    'R∨0': idx_classical_disjunction0,
    'R→1': idx_classical_conditional1,
    'R→0': idx_classical_conditional0,
    'R↔1': idx_classical_biconditional1,
    'R↔0': idx_classical_biconditional0,
}

idx_classical_closure_rules = [
    [TableauxNode(content=Formula(['A']), index=1), TableauxNode(content=Formula(['A']), index=0)]
]

classical_indexed_tableaux_system = IndexedTableauxSystem(language=classical_infinite_language,
                                                          rules=idx_classical_tableaux_rules,
                                                          closure_rules= idx_classical_closure_rules,
                                                          solver=indexed_tableaux_solver)


# ----------------------------------------------------------------------------------------------------------------------
# TABLEAUX FOR MANY VALUED LOGICS (FDE, K3, LP)
# Missing conditional and biconditional rules... I do it without them, as in Priest (2008)

FDE_double_negation_rule1 = TableauxNode(content=Formula(['~', ['~', ['A']]]), index=1)
TableauxNode(content=Formula(['A']), index=1, justification='R~~1', parent=FDE_double_negation_rule1)
'''
['~', ['~', ['A']]], 1
└── ['A'], 1 (R~~1)
'''

FDE_double_negation_rule0 = TableauxNode(content=Formula(['~', ['~', ['A']]]), index=0)
TableauxNode(content=Formula(['A']), index=0, justification='R~~0', parent=FDE_double_negation_rule0)
'''
['~', ['~', ['A']]], 0
└── ['A'], 0 (R~~0)
'''

FDE_conjunction_rule1 = TableauxNode(content=Formula(['∧', ['A'], ['B']]), index=1)
FDEcr1 = TableauxNode(content=Formula(['A']), index=1, justification='R∧1', parent=FDE_conjunction_rule1)
TableauxNode(content=Formula(['B']), index=1, justification='R∧1', parent=FDEcr1)
'''
['∧', ['A'], ['B']], 1
└── ['A'], 1 (R∧1)
    └── ['B'], 1 (R∧1)
'''

FDE_conjunction_rule0 = TableauxNode(content=Formula(['∧', ['A'], ['B']]), index=0)
TableauxNode(content=Formula(['A']), index=0, justification='R∧0', parent=FDE_conjunction_rule0)
TableauxNode(content=Formula(['B']), index=0, justification='R∧0', parent=FDE_conjunction_rule0)
'''
['∧', ['A'], ['B']], 0
├── ['A'], 0 (R∨0)
└── ['B'], 0 (R∨0)
'''

FDE_neg_conjunction_rule1 = TableauxNode(content=Formula(['~', ['∧', ['A'], ['B']]]), index=1)
TableauxNode(content=Formula(['∨', ['~', ['A']], ['~', ['B']]]), index=1, justification='R~∧1',
             parent=FDE_neg_conjunction_rule1)
'''
['~', ['∧', ['A'], ['B']]], 1
└── ['∨', ['~', ['A']], ['~', ['B']]], 1 (R~∧1)
'''

FDE_neg_conjunction_rule0 = TableauxNode(content=Formula(['~', ['∧', ['A'], ['B']]]), index=0)
TableauxNode(content=Formula(['∨', ['~', ['A']], ['~', ['B']]]), index=0, justification='R~∧0',
             parent=FDE_neg_conjunction_rule0)
'''
['~', ['∧', ['A'], ['B']]], 0
└── ['∨', ['~', ['A']], ['~', ['B']]], 0 (R~∧0)
'''

FDE_disjunction_rule1 = TableauxNode(content=Formula(['∨', ['A'], ['B']]), index=1)
TableauxNode(content=Formula(['A']), index=1, justification='R∨1', parent=FDE_disjunction_rule1)
TableauxNode(content=Formula(['B']), index=1, justification='R∨1', parent=FDE_disjunction_rule1)
'''
['∨', ['A'], ['B']], 1
├── ['A'], 1 (R∨1)
└── ['B'], 1 (R∨1)
'''

FDE_disjunction_rule0 = TableauxNode(content=Formula(['∨', ['A'], ['B']]), index=0)
FDEdr1 = TableauxNode(content=Formula(['A']), index=0, justification='R∨0', parent=FDE_disjunction_rule0)
TableauxNode(content=Formula(['B']), index=0, justification='R∨0', parent=FDEdr1)
'''
['∨', ['A'], ['B']], 0
└── ['A'], 0 (R∨0)
    └── ['B'], 0 (R∨0)
'''

FDE_neg_disjunction_rule1 = TableauxNode(content=Formula(['~', ['∨', ['A'], ['B']]]), index=1)
TableauxNode(content=Formula(['∧', ['~', ['A']], ['~', ['B']]]), index=1, justification='R~∨1',
             parent=FDE_neg_disjunction_rule1)
'''
['~', ['∨', ['A'], ['B']]], 1
└── ['∧', ['~', ['A']], ['~', ['B']]], 1 (R~∨1)
'''

FDE_neg_disjunction_rule0 = TableauxNode(content=Formula(['~', ['∨', ['A'], ['B']]]), index=0)
TableauxNode(content=Formula(['∧', ['~', ['A']], ['~', ['B']]]), index=0, justification='R~∨0',
             parent=FDE_neg_disjunction_rule0)
'''
['~', ['∨', ['A'], ['B']]], 0
└── ['∧', ['~', ['A']], ['~', ['B']]], 0 (R~∨0)
'''

FDE_tableaux_rules = {
    'R~~1': FDE_double_negation_rule1,
    'R~~0': FDE_double_negation_rule0,
    'R∧1': FDE_conjunction_rule1,
    'R∧0': FDE_conjunction_rule0,
    'R~∧1': FDE_neg_conjunction_rule1,
    'R~∧0': FDE_neg_conjunction_rule0,
    'R∨1': FDE_disjunction_rule1,
    'R∨0': FDE_disjunction_rule0,
    'R~∨1': FDE_neg_disjunction_rule1,
    'R~∨0': FDE_neg_disjunction_rule0,
}

FDE_closure_rules = [
    [TableauxNode(content=Formula(['A']), index=0),
     TableauxNode(content=Formula(['A']), index=1)]
]
K3_closure_rules = FDE_closure_rules + \
                   [[TableauxNode(content=Formula(['A']), index=1),
                     TableauxNode(content=Formula(['~', ['A']]), index=1)]]
LP_closure_rules = FDE_closure_rules + \
                   [[TableauxNode(content=Formula(['A']), index=0),
                     TableauxNode(content=Formula(['~', ['A']]), index=0)]]

FDE_tableaux_system = ManyValuedTableauxSystem(language=classical_infinite_language_noconditional,
                                               rules=FDE_tableaux_rules,
                                               closure_rules=FDE_closure_rules,
                                               solver=indexed_tableaux_solver)
K3_tableaux_system = ManyValuedTableauxSystem(language=classical_infinite_language_noconditional,
                                              rules=FDE_tableaux_rules,
                                              closure_rules=K3_closure_rules,
                                              solver=indexed_tableaux_solver)
LP_tableaux_system = ManyValuedTableauxSystem(language=classical_infinite_language_noconditional,
                                              rules=FDE_tableaux_rules,
                                              closure_rules=LP_closure_rules,
                                              solver=indexed_tableaux_solver)

# ----------------------------------------------------------------------------------------------------------------------
# TABLEAUX FOR MODAL LOGICS

modal_box_rule = TableauxNode(content=Formula(['□', ['A']]))
# USE PREDICATE FORMULAE FOR NODES OF THE FORM irj

modal_neg_box_rule = TableauxNode(content=Formula(['~', ['□', ['A']]]))
TableauxNode(content=Formula(['◇', ['~', ['A']]]), justification='R~□', parent=modal_neg_box_rule)
'''
['~', ['□', ['A']]]
└── ['◇', ['~', ['A']]] (R~□)
'''

modal_neg_diamond_rule = TableauxNode(content=Formula(['~', ['◇', ['A']]]))
TableauxNode(content=Formula(['□', ['~', ['A']]]), justification='R~◇', parent=modal_neg_diamond_rule)
'''
['~', ['◇', ['A']]]
└── ['□', ['~', ['A']]] (R~◇)
'''

# ----------------------------------------------------------------------------------------------------------------------
# CONSTRUCTIVE TREES

classical_constructive_tree_system = ConstructiveTreeSystem(language=classical_infinite_language,
                                                            solver=constructive_tree_solver)
