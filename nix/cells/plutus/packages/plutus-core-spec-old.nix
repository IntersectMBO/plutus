{ inputs, cell }:

cell.library.build-latex-doc {
  name = "plutus-core-spec-old";
  description = "Plutus core specification (old version)";
  src = inputs.self + /doc/plutus-core-spec-old;
}
