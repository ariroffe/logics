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

.. data:: logics.instances.propositional.natural_deduction.classical_natural_deduction_system2

    Alternative (but also usual) presentation of the classical natural deduction system.
    Has no repetition nor EFSQ as primitive rules. The ``E~`` rule is double negation.
    The ``I~`` rule takes a formula of the form ``A ∧ ~A`` instead of ``⊥`` as the last step
    inside the supposition. The rest is identical.

    .. literalinclude:: ../../../../logics/instances/propositional/natural_deduction.py
       :language: python
       :lines: 121-135

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

.. data:: logics.utils.solvers.classical_natural_deduction_solver2

A solver for the alternative natural deduction system.
