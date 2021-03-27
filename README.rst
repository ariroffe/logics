======
Logics
======

Logics is a Python framework for mathematical logic. It aims at generality (being able to represent as many systems
as possible), well-documented and readable code and minimal dependencies, rather than speed. Some of its intended
applications are educational software (e.g. `TAUT <https://taut-logic.com/>`_, which uses a previous version of this
package), and quick prototyping of ideas for research purposes.

To see the documentation please visit: LINK


Installation
############

To install using ``pip``:

.. code:: bash

   $ pip install logics

Or clone it from this repository:

.. code:: bash

   $ git clone https://github.com/ariroffe/logics.git


Examples
########

The following are some random examples of what you can do with this package. For a full specification of the
functionality see the documentation.

Define a language:

>>> from logics.classes.propositional import Language
>>> language = Language(atomics=['p', 'q', 'r'],
...                     constant_arity_dict={'~': 1, '∧': 2},
...                     sentential_constants=['⊥', '⊤'],
...                     metavariables=['A', 'B', 'C'],
...                     context_variables=['Γ', 'Δ', 'Σ', 'Λ', 'Π', 'Θ'])


Construct formulae and inferences/metainferences, and use specific methods of those classes:

>>> from logics.utils.parsers import classical_parser
>>> formula = classical_parser.parse('~(p and not q)')
>>> inference = classical_parser.parse('(p / p) // (q / p & not p)')
>>> type(formula)
<class 'logics.classes.propositional.inference.Inference'>
>>> type(inference)
<class 'logics.classes.propositional.inference.Inference'>
>>> formula.depth
3
>>> formula.is_well_formed(language)
True
>>> formula.is_instance_of(classical_parser.parse('not (A and B)'), language)
True
>>> formula2 = formula.substitute(classical_parser.parse("p"), classical_parser.parse("p or q"))
>>> classical_parser.unparse(formula2)
'~((p ∨ q) ∧ ~q)'
>>> inference.level
2

Define a mixed many-valued model theory, and use it:

>>> from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants
>>> from logics.classes.propositional.semantics import MixedManyValuedSemantics
>>> trivalued_truth_values = ['1', 'i', '0']
>>> trivalued_truth_functions = {
...     '~': ['0', 'i', '1'],
...     '∧': [ #1   #i   #0
...           ['1', 'i', '0'],    # 1
...           ['i', 'i', '0'],    # i
...           ['0', '0', '0']],   # 0
...     '∨': [ #1   #i   #0
...           ['1', '1', '1'],    # 1
...           ['1', 'i', 'i'],    # i
...           ['1', 'i', '0']],   # 0
...     '→': [ #1   #i   #0
...           ['1', 'i', '0'],    # 1
...           ['1', 'i', 'i'],    # i
...           ['1', '1', '1']],   # 0
...     '↔': [ #1   #i   #0
...           ['1', 'i', '0'],    # 1
...           ['i', 'i', 'i'],    # i
...           ['0', 'i', '1']],   # 0
...     }
>>> ST = MixedManyValuedSemantics(language=classical_infinite_language_with_sent_constants,
...                               truth_values=trivalued_truth_values,
...                               premise_designated_values=['1'],
...                               conclusion_designated_values=['1', 'i'],
...                               truth_function_dict=trivalued_truth_functions,
...                               sentential_constant_values_dict={'⊥': '0', '⊤': '1'},
...                               name='ST')
>>> ST.valuation(classical_parser.parse('p then q'), {'p': '1', 'q': 'i'})
'i'
>>> ST.satisfies(classical_parser.parse('(A / B), (B / C) // (A / C)'), {'A': '1', 'B': 'i', 'C': '0'})
False
>>> ST.is_valid(classical_parser.parse('p and ~p / q'))
True
>>> ST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
False
>>> ST.is_globally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
True
>>> # There are also some predefined systems (ST is one of them, the above was unnecesary)
>>> from logics.instances.propositional.many_valued_semantics import TS_mvl_semantics as TS
>>> from logics.instances.propositional.many_valued_semantics import LP_mvl_semantics as LP
>>> LP.is_valid(classical_parser.parse('p and ~p / q'))
False
>>> from logics.classes.propositional.semantics import MixedMetainferentialSemantics
>>> TSST = MixedMetainferentialSemantics([TS, ST])
>>> TSST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
True

As in `TAUT <https://taut-logic.com/>`_, logics has natural deduction module:

>>> # You can define your own natural deduction system, here we will just import a predefined instance:
>>> from logics.instances.propositional.natural_deduction import classical_natural_deduction_system
>>> from logics.utils.solvers import classical_natural_deduction_solver
>>> derivation = classical_natural_deduction_solver.solve(classical_parser.parse("A → B, ~B / ~A"))
>>> derivation.print_derivation(classical_parser)
0. A → B; premise; []
1. ~B; premise; []
|  2. A; supposition; []
|  3. B; E→; [0, 2]
|  4. ⊥; E~; [1, 3]
5. ~A; I~; [2, 4]
>>> classical_natural_deduction_system.is_correct_derivation(derivation)
True

I have now added tableaux systems:

>>> from logics.classes.propositional.proof_theories import TableauxNode
>>> # Again, you can define your own tableaux system, here I use a predefined instance
>>> from logics.instances.propositional.tableaux import classical_tableaux_system
>>> n1 = TableauxNode(content=classical_parser.parse('~~~~p'))
>>> n2 = TableauxNode(content=classical_parser.parse('~p'), parent=n1)
>>> n3 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~', parent=n2)
>>> n1.print_tree(classical_parser)
(~~~p)
└── ~p
    └── ~~p (R~~)
>>> classical_tableaux_system.node_is_closed(n2)
False
>>> classical_tableaux_system.tree_is_closed(n1)
True
>>> classical_tableaux_system.rule_is_applicable(n1, 'R~~')
True
>>> classical_tableaux_system.is_correct_tree(n1)
True
>>> # The tableaux solver (unlike ND one) will work for any arbitrary system you define
>>> tree = classical_tableaux_system.solve_tree(classical_parser.parse("~(p ∧ q) / ~p ∨ ~q"))
>>> tree.print_tree(classical_parser)
~(p ∧ q)
└── ~(~p ∨ ~q)
    ├── ~p (R~∧)
    │   └── ~~p (R~∨)
    │       └── ~~q (R~∨)
    └── ~q (R~∧)
        └── ~~p (R~∨)
            └── ~~q (R~∨)
>>> # There is even a tableaux class for indexed tableaux, here is a predefined instance
>>> from logics.instances.propositional.tableaux import LP_tableaux_system
>>> tree2 = LP_tableaux_system.solve_tree(classical_parser.parse("~(p ∨ q) / ~~p ∧ ~~q"))
>>> tree2.print_tree(classical_parser)
~(p ∨ q), 1
└── ~~p ∧ ~~q, 0
    └── ~p ∧ ~q, 1 (R~∨1)
        ├── ~~p, 0 (R∧0)
        │   └── ~p, 1 (R∧1)
        │       └── ~q, 1 (R∧1)
        │           └── p, 0 (R~~0)
        └── ~~q, 0 (R∧0)
            └── ~p, 1 (R∧1)
                └── ~q, 1 (R∧1)
                    └── q, 0 (R~~0)

And sequent calculi:

>>> sequent = classical_parser.parse("Gamma, A ==> B, Delta")
>>> classical_parser.unparse(sequent)
'Γ, A ⇒ B, Δ'
>>> sequent2 = sequent.substitute(language, "Γ", classical_parser.parse("D"))
>>> classical_parser.unparse(sequent2)
'D, A ⇒ B, Δ'
>>> # Again, you can define your sequent calculus, here I use a predefined instance
>>> from logics.instances.propositional.sequents import LK
>>> LK.sequent_is_axiom(classical_parser.parse("p or q ==> p or q"))
True
>>> from logics.classes.propositional.proof_theories import SequentNode
>>> n1 = SequentNode(content=classical_parser.parse('A ==> A'), justification='identity')
>>> n2 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WR', children=[n1])
>>> n3 = SequentNode(content=classical_parser.parse('Gamma, A ==> A, Delta'), justification='WL', children=[n2])
>>> n3.print_tree(classical_parser)  # the root of the tree is the derived node
Γ, A ⇒ A, Δ (WL)
└── A ⇒ A, Δ (WR)
    └── A ⇒ A (identity)
>>> LK.is_correct_tree(n1)
True
>>> LK.tree_is_closed(n3)
True
>>> # There is also a solver that will work whenever your system has no elimination rules
>>> # A system that the solver can work with easily, see the docs for a description
>>> from logics.instances.propositional.sequents import LKminEA
>>> tree = LKminEA.reduce(classical_parser.parse("Gamma ==> A or ~A"))
>>> tree.print_tree(classical_parser)
Γ ⇒ A ∨ ~A (∨R1)
└── Γ ⇒ A, ~A (~R)
    └── Γ, A ⇒ A (WL)
        └── A ⇒ A (identity)

There are also some predicate logic tools:

>>> from logics.classes.predicate.semantics import Model
>>> model = Model({
...     'domain': {1, 2},
...     'a': 1,
...     'b': 2,
...     'P': {1},
...     'R': {(1,1), (1,2)},
...     'f': {((1,), 2), ((2,), 1)},
...     'g': {((1, 1), 1), ((1, 2), 2), ((2, 1), 1), ((2, 2), 2)}
... })
>>> model.denotation('f')
{((2,), 1), ((1,), 1)}
>>> # Again, predefined instance, you can define this yourself
>>> from logics.instances.predicate.model_semantics import classical_functional_model_semantics
>>> classical_functional_model_semantics.valuation(parser.parse("P(a)"), model)
'1'
>>> classical_functional_model_semantics.valuation(parser.parse("R(a, b)"), model)
'1'
>>> classical_functional_model_semantics.valuation(parser.parse("R(f(a), g(f(a), b))"), model)
'0'
>>> classical_functional_model_semantics.valuation(parser.parse("exists x (P(f(x)))"), model)
'1'
>>> classical_functional_model_semantics.valuation(parser.parse("forall X (exists x (X(f(x))))"), model)
'0'
>>> # You can also define theories with fixed denotations for some terms by subclassing Model
>>> from itertools import count
>>> from logics.instances.predicate.model_subclasses import ArithmeticModel
>>> from logics.utils.parsers.predicate_parser import arithmetic_parser
>>> from logics.instances.predicate.model_semantics import arithmetic_model_semantics
>>> arithmetic_model = ArithmeticModel({'domain': count(0)})
>>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("s(0) > 0"), arithmetic_model)
'1'
>>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("s(0) + s(0) = s(s(0))"), arithmetic_model)
'1'
>>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("exists x (x = s(0))"), arithmetic_model)
'1'


And many more things! (see the documentation)


Acknowledgements
################

`logics` is a project by `Ariel Jonathan Roffé <https://sites.google.com/view/ariel-roffe/home>`_ (CONICET / University
of Buenos Aires)

Contributors to the project:

* `Joaquin S. Toranzo Calderon <https://uba.academia.edu/JoaquinToranzoCalderon>`_ (`mapped_logics` module)

The author also wishes to thank the `Buenos Aires Logic Group <https://www.ba-logic.com/>`_ who supported this project.
