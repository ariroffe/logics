Models
======

Model
-----

.. autoclass:: logics.classes.predicate.semantics.Model
   :members:

Subclasses
^^^^^^^^^^

.. data:: logics.instances.predicate.model_subclasses.ArithmeticModel

   Includes fixed denotations for '0', 's', '+', '*', '**', '=', '>', '<'

.. data:: logics.instances.predicate.model_subclasses.RealNumberArithmeticModel

   Includes fixed denotations for '+', '-', '*', '/', '//, '**', '=', '>', '<'.
   Also extends the ``denotation`` method in order in order to return one for the numerals and floats.


Model Theory
------------

.. autoclass:: logics.classes.predicate.semantics.ModelTheory
   :members:

Instances
^^^^^^^^^

.. data:: logics.instances.predicate.model_semantics.classical_model_semantics

   Model theory for second-order classical logic (for the language `classical_infinite_predicate_language`).
   No function symbols.

.. data:: logics.instances.predicate.model_semantics.classical_functional_model_semantics

   Same as the above, for the language `classical_function_language`. Is exemplified in the class above.

.. data:: logics.instances.predicate.model_semantics.arithmetic_model_semantics

   Model theory for second-order natural-number arithmetic. For the language `arithmetic_language`.

.. data:: logics.instances.predicate.model_semantics.realnumber_arithmetic_model_semantics

   Model theory for second-order real-number arithmetic. For the language `real_number_arithmetic_language`.
