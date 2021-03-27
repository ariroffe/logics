Sequents
========

Base Classes
------------

.. autoclass:: logics.classes.propositional.proof_theories.Sequent
   :members:

.. autoclass:: logics.classes.propositional.proof_theories.SequentNode
   :members:


Sequent Calculus
----------------

.. autoclass:: logics.classes.propositional.proof_theories.SequentCalculus
   :members:


Instances
^^^^^^^^^

.. data:: logics.instances.propositional.sequents.LK

   The standard LK system with Cut. The structural rules are presented with context variables. E.g. WL is:

.. code-block:: python

    weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
    weakening_left = SequentNode(content=classical_parser.parse('Pi, Gamma ==> Delta'),
                                 children=[weakening_left_premise])

This is for the solver to be able to weaken context variables in LKmin (see below).
Since LK has Cut, does have a solver (reducer) assigned.
For the full list of rules, see the source code.

.. data:: logics.instances.propositional.sequents.LKmin

   Same as the above but with no Cut rule. Has a solver (which works extremely slowly).

.. data:: logics.instances.propositional.sequents.LKminEA

   A version of LKmin that works with sequences, like everything here, but has Exchange admissible (internalized into
   the other rules). Also uses a combination of additive and multiplicative rules. All this makes it much faster to work
   with for the solver.


Sequent Reducer
---------------

.. autoclass:: logics.utils.solvers.sequents.SequentReducer
   :members:
