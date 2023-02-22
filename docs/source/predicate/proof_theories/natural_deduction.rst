Natural Deduction
=================

Base Classes
------------

The ``Derivation`` and ``NaturalDeductionStep`` classes are shared with
the propositional ND module.

.. autoclass:: logics.classes.predicate.proof_theories.PredicateNaturalDeductionRule

Natural Deduction System
------------------------

.. autoclass:: logics.classes.predicate.proof_theories.PredicateNaturalDeductionSystem

.. _pred-nd-instances:

Instances
^^^^^^^^^

.. data:: logics.instances.predicate.natural_deduction.predicate_classical_natural_deduction_system

    Has same rules as the propositional system 1, plus the following rules:

    .. literalinclude:: ../../../../logics/instances/predicate/natural_deduction.py
       :language: python
       :lines: 21-51

Natural Deduction Solver
------------------------

.. autoclass:: logics.utils.solvers.first_order_natural_deduction.FirstOrderNaturalDeductionSolver


Instances
^^^^^^^^^

.. data:: logics.utils.solvers.first_order_natural_deduction.first_order_natural_deduction_solver

A solver for the natural deduction system presented above.
