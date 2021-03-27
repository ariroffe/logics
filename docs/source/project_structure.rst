Project Structure
=================

`logics` is divided into three submodules: `classes`, `instances` and `utils`

As the names indicate, `classes` contains the class definitions, which may be thought of as metatheoretical definitions
or specifications of concepts (e.g. what a language is, what a formula is, what a many-valued system is, etc.)

`instances` contains particular instantiations of those classes for some known systems. For example, some instances
for the class ``MixedManyValuedSemantics`` include the systems `K3`, `LP`, `ST`, `TS` and classical logic.

`utils` is composed of utilities such as parsers (which allow working with ``Formula`` and ``Inference`` objects much
more easily), random formula generators, solvers, etc. In general, both the utility classes and their instances are
defined in the same file.
