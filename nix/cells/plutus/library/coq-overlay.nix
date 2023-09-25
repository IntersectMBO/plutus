{ inputs, cell }:

self: super: {
  # Coq pulls this in, but doesn't build for windows, and we don't need it.
  # It would be nicer to override the coq derivation to null the argument
  # out, but in fact the coq derivation is produced in a twisty way as part
  # of the coq package sets, so I just did this rather cruder approach that
  # works fine since we don't need this package elsewhere.
  csdp = null;
}
