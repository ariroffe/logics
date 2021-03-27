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


Instances
^^^^^^^^^

.. data:: logics.instances.propositional.tableaux.classical_tableaux_system

    Has the following rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 11-95


.. data:: logics.instances.propositional.tableaux.FDE_tableaux_system
.. data:: logics.instances.propositional.tableaux.LP_tableaux_system
.. data:: logics.instances.propositional.tableaux.K3_tableaux_system

    All three systems share the following rules (note there is no conditional nor biconditional):

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 123-203

    They only differ in their closure rules:

    .. literalinclude:: ../../../../logics/instances/propositional/tableaux.py
       :language: python
       :lines: 218-227


Tableaux Solver
---------------

.. autoclass:: logics.utils.solvers.tableaux.TableauxSolver
   :members:

.. autoclass:: logics.utils.solvers.tableaux.ManyValuedTableauxSolver