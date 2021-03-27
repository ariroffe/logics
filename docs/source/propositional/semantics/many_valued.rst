Many-Valued Semantics
=====================

..
   _Made with automethod instead of autoclass because Sphinx does not order the methods well for the :inherited-members:

Mixed Many-Valued Semantics
---------------------------

.. autoclass:: logics.classes.propositional.semantics.MixedManyValuedSemantics

    .. automethod:: apply_truth_function

    .. automethod:: valuation

    .. automethod:: truth_table

    .. automethod:: satisfies

    .. automethod:: is_locally_valid

    .. automethod:: is_locally_antivalid

    .. automethod:: is_contingent

    .. automethod:: is_valid

    .. automethod:: is_antivalid

    .. automethod:: is_tautology

    .. automethod:: is_contradiction

    .. automethod:: is_globally_valid

    .. automethod:: is_globally_valid2

    .. automethod:: is_globally_valid3

Instances
^^^^^^^^^

The following are predefined instances of MixedManyValuedSemantics.

.. data:: logics.instances.propositional.many_valued_semantics.classical_mvl_semantics

    Classical logic semantics (truth values are ``['1', '0']`` and both premise and conclusion standards are ``['1']``)

.. data:: logics.instances.propositional.many_valued_semantics.K3_mvl_semantics
.. data:: logics.instances.propositional.many_valued_semantics.LP_mvl_semantics
.. data:: logics.instances.propositional.many_valued_semantics.ST_mvl_semantics
.. data:: logics.instances.propositional.many_valued_semantics.TS_mvl_semantics

    The above four systems share the truth values ``['1', 'i', '0']``.
    If S denotes the standard ``['1']`` and T denotes de standard ``['1', 'i']``
    Then K3 is the mixed system S/S, LP is the mixed system T/T,
    ST is the mixed system S/T and T/S is the mixed system T/S


Mixed Metainferential Semantics
-------------------------------

.. autoclass:: logics.classes.propositional.semantics.MixedMetainferentialSemantics

Instances
^^^^^^^^^

.. autofunction:: logics.instances.propositional.many_valued_semantics.classical_logic_up_to_level

.. autofunction:: logics.instances.propositional.many_valued_semantics.empty_logic_up_to_level


Union and Intersection Logics
-----------------------------

.. autoclass:: logics.classes.propositional.semantics.IntersectionLogic

.. autoclass:: logics.classes.propositional.semantics.UnionLogic
