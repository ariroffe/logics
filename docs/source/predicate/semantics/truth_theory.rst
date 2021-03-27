Truth Theory
============

This module is mostly exploratory, I did it for fun, to see if something could be done.

Languages
---------

.. autoclass:: logics.classes.predicate.language.TruthPredicateLanguage

Instances
^^^^^^^^^

.. data:: logics.instances.predicate.languages.arithmetic_truth_language

   A language for arithmetic truth. Similar to the language of natural number arithmetic (see Language > Instances),
   with added unary predicate `Tr`, unary function `quote` and sentential constant `λ`.


Parsing utilities
-----------------

Godel encoding and decoding is handled by the parser.

.. autofunction:: logics.utils.parsers.parser_utils.godel_encode

.. autofunction:: logics.utils.parsers.parser_utils.godel_decode

.. autoclass:: logics.utils.parsers.predicate_parser.ArithmeticTruthParser
   :members:

Instances
^^^^^^^^^

.. data:: logics.utils.parsers.predicate_parser.arithmetic_truth_parser

   Identical to the instance defined in the example above.


Model theories
--------------

.. autoclass:: logics.classes.predicate.semantics.models.TruthPredicateModelTheory


Instances
^^^^^^^^^

.. data:: logics.instances.predicate.model_semantics.arithmetic_truth_model_semantics

   Identical to the instance defined in the example above.
