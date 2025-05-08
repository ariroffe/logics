Tableaux
========

Base Classes
------------

.. autoclass:: logics.classes.propositional.proof_theories.TableauxNode
   :members:


Tableaux System
---------------

.. autoclass:: logics.classes.propositional.proof_theories.TableauxSystem
   :members:

.. autoclass:: logics.classes.propositional.proof_theories.tableaux.ManyValuedTableauxSystem

.. autoclass:: logics.classes.propositional.proof_theories.tableaux.IndexedTableauxSystem

Instances
^^^^^^^^^

.. data:: logics.instances.propositional.tableaux.classical_tableaux_system

    Has the following rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 11-95

    Closes a branch when both A and ~A occur in it (for some formula A)

.. data:: logics.instances.propositional.tableaux.classical_indexed_tableaux_system

    Indexed presentation of classical logic. Has the following rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 124-216

    Closes a branch when both A, 1 and A, 0 occur in it (for some formula A)

.. data:: logics.instances.propositional.tableaux.FDE_tableaux_system
.. data:: logics.instances.propositional.tableaux.LP_tableaux_system
.. data:: logics.instances.propositional.tableaux.K3_tableaux_system

    All three systems share the following rules (note there is no conditional nor biconditional):

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 245-325

    They only differ in their closure rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 340-349


Systems with invertible rules
-----------------------------

The TableauxSystem class' ``is_correct_tree`` method needs the applications of rules to be made in order. For example,
if a rule like this is provided:

.. code-block::

   A ↔ B
   ├── A (R↔)
   │   └── B (R↔)
   └── ~A (R↔)
       └── ~B (R↔)

Then the following will be a correctly derived tree:

.. code-block::

   p ↔ q
   ├── p (R↔)
   │   └── q (R↔)
   └── ~p (R↔)
       └── ~q (R↔)

But the following two will not, because they do not respect the order in which the nodes are derived in the rule:

.. code-block::

   p ↔ q
   ├── q (R↔)
   │   └── p (R↔)
   └── ~p' (R↔)
       └── ~q (R↔)

   p ↔ q
   ├── ~p (R↔)
   │   └── ~q (R↔)
   └── p (R↔)
       └── q (R↔)

This may be undesirable in some circumstances, since that order should not make a difference. To fix this issue, we
simply add systems with more rules, so for instance:

.. code-block::

   A ↔ B
   ├── B (R↔)
   │   └── A (R↔)
   └── ~A (R↔)
       └── ~B (R↔)

and

.. code-block::

   A ↔ B
   ├── ~A (R↔)
   │   └── ~B (R↔)
   └── A (R↔)
       └── B (R↔)

are added as rules. These systems are built so that every possible order that does not alter the derivation is a correct
one. They are called the same as the above, but with an _invertible suffix, e.g., ``classical_tableaux_system_invertible``,
``classical_indexed_tableaux_system_invertible``, ``FDE_tableaux_system_invertible``, ``K3_tableaux_system_invertible``,
``LP_tableaux_system_invertible``

Tableaux Solver
---------------

.. autoclass:: logics.utils.solvers.tableaux.TableauxSolver
   :members:

.. autoclass:: logics.utils.solvers.tableaux.IndexedTableauxSolver


Constructive Tree System
------------------------

.. autoclass:: logics.classes.propositional.proof_theories.tableaux.ConstructiveTreeSystem
   :members:
