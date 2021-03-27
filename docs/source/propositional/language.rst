Language
========

.. autoclass:: logics.classes.propositional.Language
   :members:

.. autoclass:: logics.classes.propositional.InfiniteLanguage


Instances
---------

The following are predefined instances of Language and InfiniteLanguage.

.. data:: logics.instances.propositional.languages.classical_language

    Classical finite language.
    Contains atomics `p`, `q`, `r`, `s`, `t`, metavariables `A`, `B`, `C`, `D` constants `~`, `∧`, `∨`, `→`, `↔` and
    context variables `Γ`, `Δ`, `Σ`, `Λ`, `Π`, `Θ`.

.. data:: logics.instances.propositional.languages.classical_infinite_language

    Same as above but with an indefinite supply of atomics and metavariables

.. data:: logics.instances.propositional.languages.classical_language_with_sent_constants,
          logics.instances.propositional.languages.classical_infinite_language_with_sent_constants

    Same as the two above, adding the sentential constants `⊥`, `⊤`

.. data:: logics.instances.propositional.languages.classical_infinite_language_noconditional

    Same as the second, with constants `~`, `∧`, `∨`.

.. data:: logics.instances.propositional.languages.classical_infinite_language_nobiconditional
          logics.instances.propositional.languages.classical_infinite_language_with_sent_constants_nobiconditional

    Same as the second and fourth, with constants `~`, `∧`, `∨`, `→`.

.. data:: logics.instances.propositional.languages.classical_infinite_language_only_negation_conditional

    Same as the second, with constants `~`, `→`.

.. data:: logics.instances.propositional.languages.modal_language

    Same as `classical_language` but adds the unary constants `□` and `◇`

.. data:: logics.instances.propositional.languages.modal_infinite_language

    Same as the one immediately above, with an indefinite supply of atomics and metavariables

.. data:: logics.instances.propositional.languages.modal_infinite_language_with_sent_constants

    Same as the one immediately above, adding the sentential constants `⊥`, `⊤`
