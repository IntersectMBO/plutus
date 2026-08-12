### Changed

- When the PIR inliner calculates the size of a term, it now excludes type and kind nodes.
  This should approximate the serialized size better, and it also makes the inlining
  behavior more consistent.
