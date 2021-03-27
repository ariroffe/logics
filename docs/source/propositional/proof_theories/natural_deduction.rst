Natural Deduction
=================

Base classes
------------

.. autoclass:: logics.classes.propositional.proof_theories.NaturalDeductionStep

.. autoclass:: logics.classes.propositional.proof_theories.NaturalDeductionRule


Natural Deduction System
------------------------

.. autoclass:: logics.classes.propositional.proof_theories.NaturalDeductionSystem
   :members:

.. _prop-nd-instances:

Instances
^^^^^^^^^

.. data:: logics.instances.propositional.natural_deduction.classical_natural_deduction_system

    Has the following rules:

    .. literalinclude:: ../../../../logics/instances/propositional/natural_deduction.py
       :language: python
       :lines: 8-109


Natural Deduction Solver
------------------------

.. autoclass:: logics.utils.solvers.natural_deduction.NaturalDeductionSolver
   :members:

.. autoclass:: logics.utils.solvers.natural_deduction.Heuristic
   :members:


Instances
^^^^^^^^^

.. data:: logics.utils.solvers.classical_natural_deduction_solver

A solver for the natural deduction system presented above.
