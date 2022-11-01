# Changelog

This will record all the major changes to the spec for Plutus Core

At the present time, versioning is of the form `RCn` for Release Candidate #n.





## RC7 - 2019-01-20

	

### Added

- Add CHANGELOG.md to track changes.



### Changed

- Changes the lexical syntax for sizes to include the `bytes` suffixe so that
  one can write, e.g., `10bytes` instead of just `10` for sizes.

- Replaces the old definition of fixed points with the new canonical indexed
  fixed point definition of fixed point types.

- Replaces the reduction based type equality with declarative equality of types
  that includes standard properties for equality (i.e. symmetry, transitivity,
  and congruence).



### Fixed

- Fix typos in the definition of the CK machine that used just a return value
  instead of a machine state.

- Fix a bug in the definition of bounded type reduction that made not sense,
  wherein it was somehow return the *term* `(error A)` instead of simply being
  impossible to reduce. This obviously is nonsensical because types don't reduce
  to terms.

- Fix typo in the list of abbreviations that left `builtinT` in place instead of
  changing it to `conT`.

- Fix inconsistency between type frames and term frames, where type frames were
  not named as such, and required the hole to be explicitly written, while the
  term frames were named as such and did not require the hole to be explicity\
  written. The new form is that all are explicitly named as frames and the holes
  need not be written.
