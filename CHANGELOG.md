# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.1.2] - 2022-11-01
### Added
- Added a Changelog

### Changed
- Error messages on `logics.classes.propositional.proof_theories.natural_deduction`.
  `NaturalDeductionSystem`'s `is_correct_derivation` method now returns a list of tuples 
  as `error_list`, where the first member is the step index (`int`) and the second is an 
  `str` with the error, instead of a list of `str`.
