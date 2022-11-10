# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
