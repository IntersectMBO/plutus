# Generating a Cost Model

Generating a cost model for CPU time involves a number of steps.

*  Run `cabal bench plutus-core:cost-model-budgeting-bench` on the
  reference machine.  This will run Criterion benchmarks for the built-in
  functions and will take many hours.  Each function is run many times with a
  selection of inputs of different sizes.  The benchmarks for the builtins are
  small, executing single Plutus Core terms on the CEK machine.

*  The results of the benchmarks (execution versus sizes of inputs) are
   stored in a CSV file called `benching.csv` in `plutus-core/cost-model/data`.
   There's a checked-in copy [here](./data/benching.csv).

* Run `cabal bench plutus-core:update-cost-model`.  This runs some R code in
  [`plutus-core/cost-model/data/models.R`](./data/models.R) which fits a linear
  model to the data for each builtin; the general form of the model for each
  builtin is coded into `models.R`. Certain checks are performed during this
  process: for example it is possible that R will generate a model with a
  negative coefficient (for example if the results for a builtin are roughly
  constant) and if that happens then a warning is printed and the coefficient is
  replaced by zero.

*  The form of the models for each builtin, together with the model
  coefficients fitted by R, are stored in the JSON file
  [`plutus-core/cost-model/data/builtinCostModel.json`](./data/builtinCostModel.json).
  The model coefficients are converted from floating point numbers to 64-bit
  integers (representing times in picoseconds) in order to ensure
  reproducibility of results on different platforms (and we have in fact
  observed differences in the final decimal places of the output of the R models
  on different machines).

*  When the rest of the `plutus-core` package is compiled, the contents of
  `builtCostModel.json` are read and used by some Template Haskell code to
  construct Haskell functions which implement the cost models.

* To ensure consistency, `cabal bench plutus-core:cost-model-test` runs some
  QuickCheck tests to run the R models and the Haskell models and checks that
  the results agree to a reasonable level of accuracy (one part in 100, or one
  percent).  We do not expect the results to agree precisely because the R
  models perform floating-point calculations and the Haskell versions use 64-bit
  integers.  It seems that the tests hang very occasionally, perhaps because of
  some unsafe operations intereacting with the R runtime, so these tests are
  currently disguised as benchmarks to prevent them being run in CI. **The tests
  should therefore be run manually whenever new cost models are added or the R
  code is modified.**

* (Not yet automated).  After the cost model for builtins has been generated we
  run some more benchmarks which consist of entire Plutus core programs making
  limited use of builtins.  We run the benchmarks, subtract the total time for
  builtin execution as predicted by the builtin cost model, and divide the
  remaining time by the number of basic machine steps executed to arrive at an
  average time for each machine step (see the earlier discussion).  This is then
  stored in another JSON file
  [`plutus-core/cost-model/data/cekMachineCosts.json`](./data/cekMachineCosts.json).
  This cost is currently the same for each step, but more careful testing may
  enable us to produce more precise costs per step at some future date.  The
  JSON file also contains a constant cost for machine startup (perhaps a
  misnomer): this cost is currently zero, but experiments hint that there is an
  element of overall execution time which cannot be explained purely by code
  execution. This perhaps depends on the size of the AST or the number of unique
  AST nodes which are visited during program execution, but we have not yet been
  able to pin down precisely what is going on, and in any case this effect
  appears to be relatively small.

*  We can now assign a cost to an arbitrary Plutus Core program by running it
   and adding up the costs for each machine step and for each evaluation of a
   built-in function (as given by the function's cost model applied to the
   argument sizes).  This can be done automatically with `uplc evaluate --counting`
   (see [plutus-core/executables](../../plutus-core/executables)).


### Note

We use `cabal bench` to run `cost-model-budgeting-bench` and `update-cost-model`
to make sure that the program reads and writes files in
`plutus-core/cost-model/data/`.  It might be more convenient to supply the
location on the command line, and perhaps use `paths` to locate the `models.R`
file.  It would also be useful to supply a path to `cost-model-budgeting-bench`
for output of the CSV results, but this is tricky because Criterion supplies the
`main` function and does its own argument processing.
