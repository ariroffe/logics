Mapped Many-Valued Semantics
============================

Module by Joaquin S. Toranzo Calderon


Mapped Many-Valued Semantics
----------------------------

.. autoclass:: logics.classes.propositional.semantics.mapped_logic.MappedManyValuedSemantics
   :members:

Instances
^^^^^^^^^

The following are two-valued predefined instances of MappedManyValuedSemantics.

.. data:: logics.instances.propositional.mapped_logic_semantics.two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic

    Classical logic semantics (truth values are ``['1', '0']``, premises receives a universal interpretation,
    and conclusions receives an existential interpretation): Truth preservation in a bivalent frame.

.. data:: logics.instances.propositional.mapped_logic_semantics.two_valued_falsity_preservation_from_all_premises_to_some_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.two_valued_truth_preservation_from_all_premises_to_all_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.two_valued_falsity_preservation_from_all_premises_to_all_conclusions_logic


The following are three-valued predefined instances of MappedManyValuedSemantics.

.. data:: logics.instances.propositional.mapped_logic_semantics.three_valued_tolerant_strict_from_all_premises_to_some_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.three_valued_tolerant_tolerant_from_all_premises_to_some_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.three_valued_strict_strict_from_all_premises_to_some_conclusions_logic
.. data:: logics.instances.propositional.mapped_logic_semantics.intersective_mixed_logic_between_ss_and_tt_relations_all_some_logic

    The above five systems share the truth values ['1', 'i', '0'].
    The first four systems are the mixed systems TS, TT, ST and SS, in that order.
    The last one is the intersection between SS and TT.
    They all receive a universal interpretation for premises and an existential interpretation for conclusions.

