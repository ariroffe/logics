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

.. data:: logics.instances.propositional.tableaux.classical_indexed_tableaux_system

    Indexed presentation of classical logic. Has the following rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 124-216

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


Tableaux Solver
---------------

.. autoclass:: logics.utils.solvers.tableaux.TableauxSolver
   :members:

.. autoclass:: logics.utils.solvers.tableaux.IndexedTableauxSolver


Constructive Tree System
------------------------

.. autoclass:: logics.classes.propositional.proof_theories.tableaux.ConstructiveTreeSystem
   :members:
