# Cost Model

## To regenerate costModel.json

```bash
$(nix-build default.nix -A haskell.projectPackages.language-plutus-core.components.benchmarks.language-plutus-core-create-cost-model)/bin/language-plutus-core-create-cost-model
```

## To rerun the benching data

```bash
rm language-plutus-core/budgeting-bench/csvs/benching.csv
$(nix-build default.nix -A haskell.projectPackages.language-plutus-core.components.benchmarks.language-plutus-core-budgeting-bench)/bin/language-plutus-core-budgeting-bench
```

## Note [Creation of the Cost Model]

The overall goal of this module is to create the functions and calibrate the numbers which accurately predict how much each builtin (and each CEK step) will cost a node. From that we derive how much a script should cost.

### Dataflow

#### budgeting-bench

The code in budgeting-bench runs a benchmark for each `Builtin` (as defined in `Language.PlutusCore.Core.Type`). Because the inputs to the costing model are not the values passed to the builtin function, but rather its sizes, these values are stored in the csv. This may have to change for a few builtins, e.g. `TakeBytestring`, because the complexity there depends on the input values as well, instead of just the size of it. The benchmarks aim to cover a wide range of input sizes, and are generated with a predefined seed, so the generated values don't differ between runs.

#### create-cost-model

From that csv, a model is being calibrated and generated. Depending on the `Builtin`, we choose a model (by hand) and calibrate it with the benchmark data from the csv. To check which `Builtin` uses which model, consult with `models.R`. The models are created in R and invoked via `inline-r`, because of the superior modeling capacities in R. The prediction part of the model is reimplemented in Haskell.

## Add a new kind of model

I'm using vscode with its R integration. Any editor/IDE where you can evaluate R from a text file should do.
How to make a new model:

- `models.R`: evaluate the `library` imports
- `graphs.R`: evaluate the `library` imports
- `graphs.R`: edit the options on top as required
- `models.R`: evaluate the `benchData` line
- `models.R`: uncomment & evaluate the `path` line
- `models.R`: add your model to `models.R`, in the function `modelFun`, evaluate `data`, evaluate your model inside the function.
- `graphs.R`: edit `filtered` and the `plotErrorModel` call with the correct names, evaluate
- repeat as required
- `ExBudgeting.hs`: add the haskell version of the predictor
- `CostModelCreation.hs`: add code to load the model from R code
- Fix compile errors until `language-plutus-core-test-cost-model` runs & run it.
