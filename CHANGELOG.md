# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.7.1] - 2024-01-29
### Added
- WK-schema instances for metainferential tableaux

## [1.7] - 2023-10-20
### Added
- Classes, instances and solvers for metainferential tableaux

### Fixed
- Various bug fixes in tableaux systems

## [1.6.6] - 2023-08-31
### Fixed
- Natural deduction derivations cannot end with open supopsitions.

## [1.6.5] - 2023-08-18
### Changed
- If the different versions of an ND system's rule return the same
  error in its application, return that error instead of a generic error message.

### Fixed
- Use ``license_files`` instead of ``license_file`` (deprecated) in ``setup.cfg``

## [1.6.4] - 2023-08-18
### Fixed
- Natural deduction system's ``check_derivation`` method now detects if you close 
  a supposition that is not the last open one.

## [1.6.3] - 2023-04-10
### Added
- Added versions of the natural deduction systems with reversible ``on_steps``.

## [1.6.2] - 2023-03-17
### Changed
- Removed the ``category`` attribute from ``CorrectionError`` (is now inferrable
  from the numeric error code)

## [1.6.1] - 2023-03-16
### Added
- Shortcut for importing the classical predicate parser

### Changed
- Small change in the project's README

## [1.6.0] - 2023-03-16
### Added
- Extra parameter ``exit_on_first_error`` for Tableaux and SequentCalculus
  ``is_correct_tree`` mathod, and AxiomSystem's ``is_correct_derivation``.

### Changed
- Every module's ``is_correct_xxx`` method now returns a list of  
  ``logics.classes.errors.Correctionerror`` objects if asked to return the error list. 

## [1.5.0] - 2023-02-28
### Added
- Indexed presentation of classical logic tableaux.

### Changed
- Renamed ``ManyValuedTableauxSolver`` and ``mvl_tableaux_solver`` to
  ``IndexedTableauxSolver`` and ``indexed_tableaux_solver``


## [1.4.1] - 2023-02-23
### Fixed
- Bug fix in predicate parser, now correctly parsing sentences with sentential 
  metavariables.

## [1.4.0] - 2023-02-23
### Changed
- Quantified formulae given to the predicate parser should not contain parentheses
  (e.g. `"∀x P(x)"` instead of `"∀x (P(x))"`)

## [1.3.0] - 2023-02-22
### Added
- Predicate natural deduction.

### Changed
- Predicate languages now accept individual and variable metavariables 
  (they are useful for formulating rules).
  The relevant `PredicateFormula` methods were changed to account for this.

## [1.2.1] - 2022-11-15
### Added
- Alternative natural deduction system for classical logic (with solver), see docs.

### Changed
- Tableaux `is_correct_tree` errors are sorted by LevelOrder.

## [1.2.0] - 2022-11-14
### Added
- `child_index` property to `TableauxNode`.
- More extensive tests for `TableauxSystem`'s `is_correct_tree` method.

### Changed
- Error messages on `logics.classes.propositional.proof_theories.tableaux`.
  `TableauxSystem`'s `is_correct_tree` method now returns a list of tuples 
  as `error_list`, where the first member is the tuple of indexes (`int`) leading to the 
  node from the root and the second is an `str` with the error, instead of a list of `str`.

## [1.1.6] - 2022-11-10
### Fixed
- Various bugs with TableauxSystem's `is_correct_tree` (no missing premises -avoids
  marking tableaux that only contain one premise as correct-; all premises must come at 
  the beginning of the tableaux, before branching and before applying any other rule)

## [1.1.5] - 2022-11-09
### Changed
- TableauxSystem's `is_correct_tree` method now takes an extra `parser` optional parameter 
  for nicer error displaying. 

## [1.1.4] - 2022-11-04
### Added
- Option to `exit_on_first_error` in natural deduction `is_correct_derivation`

## [1.1.3] - 2022-11-04
### Changed
- Natural deduction `is_correct_derivation` accepts rule justifications like `E∧` for
  rules that have multiple versions (e.g. `E∧1`, `E∧2`)

### Fixed
- Bug fix in natural deduction's `is_correct_derivation` (do not check correct application 
  of the rule if invalid rule name)


## [1.1.2] - 2022-11-01
### Added
- Added a Changelog

### Changed
- Error messages on `logics.classes.propositional.proof_theories.natural_deduction`.
  `NaturalDeductionSystem`'s `is_correct_derivation` method now returns a list of tuples 
  as `error_list`, where the first member is the step index (`int`) and the second is an 
  `str` with the error, instead of a list of `str`.
