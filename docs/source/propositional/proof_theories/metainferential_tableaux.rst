Metainferential Tableaux
========================

Classes for metainferential tableaux, of the kind described in **(citation needed)**

Base Classes
------------

.. autoclass:: logics.classes.propositional.proof_theories.metainferential_tableaux.MetainferentialTableauxStandard
   :members:

.. autoclass:: logics.classes.propositional.proof_theories.metainferential_tableaux.MetainferentialTableauxNode

Metainferential Tableaux System
-------------------------------

.. autoclass:: logics.classes.propositional.proof_theories.metainferential_tableaux.MetainferentialTableauxSystem

Instances
^^^^^^^^^

.. data:: logics.instances.propositional.metainferential_tableaux.CL_metainferential_tableaux_system

   Tableaux system for every metainferential logic, of any level, using the `CL` (two-valued classical) schema

.. data:: logics.instances.propositional.metainferential_tableaux.SK_metainferential_tableaux_system

   Tableaux system for every metainferential logic, of any level, using the `SK` (three-valued strong Kleene) schema
   (see *citation needed*, examples below)


.. data:: logics.instances.propositional.metainferential_tableaux.WK_metainferential_tableaux_system

   Tableaux system for every metainferential logic, of any level, using the `WK` (three-valued weak Kleene) schema
   (see *citation needed*)


Metainferential Tableaux Solver
-------------------------------

.. autoclass:: logics.utils.solvers.tableaux.MetainferentialTableauxSolver
