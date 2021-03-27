Parsers
=======

.. autoclass:: logics.utils.parsers.predicate_parser.PredicateParser
   :members:


Instances
---------

.. data:: logics.utils.parsers.predicate_parser.classical_predicate_parser

   Parser for ``classical_function_language`` (see Language > Instances). Also works for the predicate languages
   without function symbols. Uses ``"forall "`, ``"exists "`` and ``" in "`` for quantified formulae.

.. data:: logics.utils.parsers.predicate_parser.arithmetic_parser

   Similar to the above example. Defined for ``arithmetic_language`` (see Language > Instances). Thus, has only ``0`` as
   individual constant (the rest of the numerals cannot be used). To refer to the rest of the natural numbers, you can
   use the ``s`` (successor) function.

.. data:: logics.utils.parsers.predicate_parser.realnumber_arithmetic_parser

   Identical to the parser defined above. Can use all the numerals (and floats, such as ``"0.5"``) as constants.
