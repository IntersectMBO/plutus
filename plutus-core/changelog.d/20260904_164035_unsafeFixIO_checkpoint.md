### Changed

- Use transitive closure in UPLC inliner certifier to avoid exponential blowups.
  The inliner is updated to perform multiple rounds of inlining, with a checkpoint
  emitted in between two rounds.
