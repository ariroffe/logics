Language
========

.. autoclass:: logics.classes.predicate.PredicateLanguage
   :members:

.. autoclass:: logics.classes.predicate.InfinitePredicateLanguage


Instances
---------

Abstract/logical languages:

.. data:: logics.instances.predicate.languages.classical_predicate_language

   Finite language, with constants `a`, `b`, `c`, `d`; Variables `x`, `y`, `z`;
   Predicate letters `P` (1), `Q` (1), `R` (2), `S` (3); Predicate variables `X` (1), `Y` (1), `Z` (2);
   Metavariables `A`, `B`, `C`; Sentential constants `⊥`, `⊤`;
   Constants `~`, `∧`, `∨`, `→`, `↔` and Quantifiers `∀`, `∃`.

.. data:: logics.instances.predicate.languages.classical_infinite_predicate_language

   InfiniteLanguage version of the above.

.. data:: logics.instances.predicate.languages.classical_function_language

   Identical to the InfiniteLanguage above, adding `f` (1) and `g` (2) function symbols.


Arithmetic languages:

.. data:: logics.instances.predicate.languages.arithmetic_language

   Identical to the `arithmetic_language` defined above in the examples.

.. data:: logics.instances.predicate.languages.real_number_arithmetic_language

   Similar to `arithmetic_language` above, but will accept any string convertible to an int or a float as constant.
   Also adds binary functions `/` and `//` (intuitively division and integer division).
