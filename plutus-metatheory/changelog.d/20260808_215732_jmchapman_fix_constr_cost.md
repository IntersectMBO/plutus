### Fixed

- Fixed the Agda metatheory's `cekMachineCostFunction` calling `getCekConstCost` instead of `getCekConstrCost` for the `Constr` case, a copy-paste bug that would silently mis-cost `Constr`-containing terms once a cost-model update sets the two parameters apart.
