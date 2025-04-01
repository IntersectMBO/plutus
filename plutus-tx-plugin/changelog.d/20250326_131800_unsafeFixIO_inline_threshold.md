
### Added

- Plinth compiler flag `inline-callsite-growth`, for setting the inlining threshold
  for callsites. 0 disables inlining a binding at a callsite if it increases the AST size;
  `n` allows inlining if the AST size grows by no more than `n`. Keep in mind that
  doing so does not mean the final program will be bigger, since inlining can often
  unlock further optimizations.
