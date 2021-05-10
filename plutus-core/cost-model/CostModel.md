# Cost Model


## To rerun the benching data

```bash
cabal bench plutus-core:cost-model-budgeting-bench
```
or
```bash
cd <path-to-plutus-repository>/plutus-core
$(nix-build .../default.nix -A plutus.haskell.packages.plutus-core.components.benchmarks.cost-model-budgeting-bench)/bin/cost-model-budgeting-bench
```
This runs microbenchmarks for built-in functions and writes the results into `plutus-core/cost-model/data/benching.csv`.  This will take many hours.
If `benching.csv` already exists then it will be copied into `benching.csv.backup` and replaced with the new results.

## To regenerate costModel.json

```bash
cabal bench plutus-core:update-budgeting-bench
```
or
```bash
cd <path-to-plutus-repository>/plutus-core
$(nix-build ../default.nix -A plutus.haskell.packages.plutus-core.components.benchmarks.update-cost-model)/bin/update-cost-model
```
This reads the benchmark results in `benching.csv`, constructs linear cost
functions using R, and writes the results into
`plutus-core/cost-model/data/costModel.json`.  This data is used by the Plutus
Core evaluator to calculate costs of built-in function invocations during
execution of Plutus Core scripts.


## Note [Creation of the Cost Model]

The overall goal of this module is to create the functions and calibrate the
numbers which accurately predict how much each builtin (and each CEK step) will
cost a node. From that we derive how much a script should cost.

### Dataflow

#### budgeting-bench

The code in budgeting-bench runs a benchmark for each `Builtin` (as defined in
`PlutusCore.Core.Type`). Because the inputs to the costing model are not the
values passed to the builtin function, but rather their sizes, these values are
stored in the csv. This may have to change for a few builtins,
e.g. `TakeBytestring`, because the complexity there depends on the input values
as well, instead of just their sizes. The benchmarks aim to cover a wide
range of input sizes and are generated with a predefined seed so the generated
values don't differ between runs.

#### create-cost-model

From `benching.csv`, a model is calibrated and generated. Depending on the
`Builtin`, we choose a model (by hand) and calibrate it with the benchmark data
from the csv. To check which `Builtin` uses which model, consult
`models.R`. The models are created in R and invoked via `inline-r` because of
the superior modeling capacities in R. The prediction part of the model is
reimplemented in Haskell for efficiency, and there are tests in
`plutus-core:cost-model-test` which checks that the Haskell versions
produce the same values as the R versions.

## Add a new kind of model
[This is somewhat superseded: a forthcoming document will provide an update.]

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
- `ExBudgeting.hs`: add the Haskell version of the predictor
- `CostModelCreation.hs`: add code to load the model from R code
- Fix compile errors until `plutus-core-test-cost-model` runs & run it.



# Calibration

Given a fully-applied Plutus Core program, the cost model is used to produce
numbers which predict upper bounds for execution time and memory usage on a
reference machine.  Assuming some homogeneity in hardware, these bounds should
provide an estimate of relative execution costs on other machines as well.  On a
specific machine it should be possible to perform some calibration to determine
a multiplier which will allow cost predictions to be adjusted to fit a given
machine.  For example, we might be able to determine that a specific machine
typically runs at 1.2 times the speed of our reference machine and that our
execution time prediction should therefore be divided by 1.2 to give an estimate
of the execution time on the machine.  For greater accuracy it may be possible
to calibrate individual operations on a per-machine basis, but this possibility
has not been explored in detail yet.


## CPU

The CPU calibration is according to the time used by a built-in operation as
determined by Criterion on our reference machine. In addition to evaluation of
built-in operations there is some overhead per step of the Plutus Core
evaluator.  This overhead is included in the cost model:  the procedure for
determining the overhead will be described in a later document.


## Memory

The memory cost per builtin operation on integers is the expected worst-case
cost of the generated value. This way the computation stays simple. If Plutus
were to adjust the usage down to actual cost, the maximum and the current usage
would have to be carried around separately: otherwise the counting mode would
predict less than the possible top amount of memory than the budgeting mode
actually requires.
