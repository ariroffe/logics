Welcome to logics' documentation!
=================================

Logics is a Python framework for mathematical logic. It aims at generality (being able to represent as many systems
as possible), well-documented and readable code and minimal dependencies, rather than speed. Some of its intended
applications are educational software (e.g. `TAUT <https://taut-logic.com/>`_, which uses a previous version of this
package), and quick prototyping of ideas for research purposes.

.. raw:: html

   <hr>

Table of Contents
=================

.. toctree::
   :maxdepth: 1
   :caption: Installation and Setup

   setup
   project_structure


.. toctree::
   :maxdepth: 1
   :caption: Propositional Logics

   propositional/language
   propositional/formula
   propositional/inference
   propositional/parsers
   propositional/formula_generators
   propositional/semantics/many_valued
   propositional/semantics/mapped_logic
   propositional/proof_theories/axiom_system
   propositional/proof_theories/natural_deduction
   propositional/proof_theories/tableaux
   propositional/proof_theories/sequents

.. toctree::
   :maxdepth: 1
   :caption: Predicate Logics

   predicate/language
   predicate/formula
   predicate/parsers
   predicate/semantics/models
   predicate/semantics/truth_theory


.. raw:: html

   <hr>


Code
====

`GitHub repository <https://github.com/ariroffe/logics>`_

:doc:`Contributing Guidelines <./contributing>`


Other References
================

`Ariel Jonathan Roffé <https://sites.google.com/view/ariel-roffe/home>`_

`Buenos Aires Logic Group <https://www.ba-logic.com/>`_
