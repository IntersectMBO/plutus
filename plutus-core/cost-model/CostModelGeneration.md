# Generating a Cost Model

Generating a cost model for CPU time involves a number of steps.

* Run `cabal run plutus-core:cost-model-budgeting-bench -- --csv <file>` on the
  reference machine.  This will run Criterion benchmarks for the built-in
  functions and will take many hours.  Each function is run many times with a
  selection of inputs of different sizes.  The benchmarks for the builtins are
  small, executing single Plutus Core terms on the CEK machine.

* The results of the benchmarks (execution versus sizes of inputs) are
  stored in CSV format in the file named in the `--csv` option, which is mandatory.

* Change directory to `plutus-core/cost-model/data/` and run `cabal run
  plutus-core:generate-cost-model -- --csv <file>`, where `<file>` is the CSV file
  produced by `cost-model-budgeting-bench`.  This runs some R code in
  [`plutus-core/cost-model/data/models.R`](./data/models.R) which fits a linear
  model to the data for each builtin; the general form of the model for each
  builtin is coded into `models.R`. Certain checks are performed during this
  process: for example it is possible that R will generate a model with a
  negative coefficient (for example if the results for a builtin are roughly
  constant) and if that happens then a warning is printed and the coefficient is
  replaced by zero.

  * When a new built-in function is added, new benchmarks will have to be added
    in `plutus-core/cost-model/budgeting-bench` and new R code will have to be
    added in `models.R` to process the results of the benchmark.  The benchmarks
    should aim to cover a wide range of inputs in order to get a good idea of
    the worst-case behaviour of the function.  The exact form of the R code will
    depend on the behaviour of the function being added and will probably be
    based on the expected time complexity of the function, backed up by
    examination of the initial benchmark results.  In simpler cases it may be
    possible to re-use existing R code, but sometimes more complex code may be
    required to obtain a good model of the behaviour of the function.  Ideally
    the R model should accurate over a wide range of inputs so that charges for
    "typical" inputs are reasonable but worst-case inputs which require large
    computation times incur large charges which penalise excessive computation.
    Some experimentation may be required to achieve this, and it may not always
    be possible to satisfy both goals simultaneously.  In such cases it may be
    necessary to sacrifice some accuracy in order to guarantee security.

* The output of `generate-cost-model` is a JSON object describing the form of
  the models for each builtin, together with the model coefficients fitted by R.
  By default this is written to the terminal, but an output file can be
  specified with `-o`.  The model coefficients are converted from floating point
  numbers to 64-bit integers (representing times in picoseconds) in order to
  ensure reproducibility of results on different platforms (and we have in fact
  observed differences in the final decimal places of the output of the R models
  on different machines).

* The specific cost model data to be used by the Plutus Core evaluator should be
  checked in to git in the file
  [`plutus-core/cost-model/data/builtinCostModel.json`](./data/builtinCostModel.json).
  The CSV file containing the benchmark results used to generate the cost model
  should be checked in in
  [`plutus-core/cost-model/data/benching.csv`](./data/benching.csv); this is not
  strictly necessary but it can be useful to have the raw data available if
  the details of the cost model need to be looked at at some later time.
  
* When the rest of the `plutus-core` package is compiled, the contents of
  `builtCostModel.json` are read and used by some Template Haskell code to
  construct Haskell functions which implement the cost models.  When a new
  built-in function is added, a circularity problem may arise where a costing
  function for the new function is required in the JSON data when the
  newly-added function is being compiled, at a point where we have not yet been
  able to run the benchmarks.  See the Note "Modifying the Cost Model" in
  [`PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs`](../plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs)
  for how to deal with this.  (See also the extensive notes on "How to add a
  built-in function" in
  [`PlutusCore/Default/Builtins.hs`](../plutus-core/src/PlutusCore/Default/Builtins.hs)
  for technical details of how to implement a new built-in function).

* To ensure consistency, `cabal bench plutus-core:cost-model-test` runs some
  QuickCheck tests to run the R models and the Haskell models and checks that
  the results agree to a reasonable level of accuracy (one part in 100, or one
  percent).  We do not expect the results to agree precisely because the R
  models perform floating-point calculations and the Haskell versions use 64-bit
  integers.  It seems that the tests hang very occasionally, perhaps because of
  some unsafe operations intereacting with the R runtime, so these tests are
  currently disguised as benchmarks to prevent them being run in CI. **The tests
  should therefore be run manually whenever new cost models are added or the R
  code is modified.** (Also, remember to add new tests when a new builtin is added).

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

