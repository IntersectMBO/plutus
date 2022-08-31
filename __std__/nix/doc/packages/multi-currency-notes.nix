{ inputs, cell }:

cell.library.build-latex-doc {
  name = "multi-currency-notes";
  src = inputs.self + /notes/multi-currency;
  description = "Multi-currency paper";
}
