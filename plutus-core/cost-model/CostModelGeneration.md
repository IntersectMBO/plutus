# Generating and Updating the Plutus Core Cost Model

This file describes how to generate or update a cost model for Plutus Core. We
start by describing how to update an existing cost model.  In the [second
section](#adding-a-new-built-in-function-and-a-suitable-costing-function) we
describe how to extend the cost model when a new built-in function is added.

## Updating an existing cost model

A cost model for Plutus Core consists of two components:

* A collection of models for individual built-in functions, each consisting of
  two costing functions: one for CPU usage and one for memory usage.

* A separate model for the costs of the basic steps of the evaluator.

We may wish to update these periodically, for example if the internal
infrastructure that supports built-in functions has changed or if the
implementation of a particular builtin has changed.  Updating the CPU time
costing functions involves a number of steps.

* Run `cabal run plutus-core:cost-model-budgeting-bench -- --csv <file>` on the
  reference machine.  This will run Criterion benchmarks for the built-in
  functions and will take many hours.  Each function is run many times with a
  selection of inputs of different sizes.  The benchmarks for the builtins are
  small, executing single Plutus Core terms on the CEK machine.  The results of
  the benchmarks (execution times versus sizes of inputs) are stored in CSV
  format in the file named in the `--csv` option, which is mandatory.  (To keep
  the cost model consistent we currently require that all benchmarks are run on
  a particular machine that is only available to the Plutus Core developers;
  eventually some community process will be developed for adding new builtins
  and approving their implementations and costing functions, but this is not
  feasible at the moment.)

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
  construct Haskell functions which implement the cost models.  

* To ensure consistency, `cabal bench plutus-core:cost-model-test` runs some
  QuickCheck tests to run the R models and the Haskell models and checks that
  the results agree to a reasonable level of accuracy (one part in 100, or one
  percent).  We do not expect the results to agree precisely because the R
  models perform floating-point calculations and the Haskell versions use 64-bit
  integers.  It seems that the tests hang very occasionally, perhaps because of
  some unsafe operations interacting with the R runtime, so these tests are
  currently disguised as benchmarks to prevent them being run in CI. **The tests
  should therefore be run manually whenever new cost models are added or the R
  code is modified.** (Also, remember to add new tests when a new builtin is added).

* (Not yet automated).  After the cost model for builtins has been
  generated we run some more benchmarks which consist of entire Plutus
  core programs making limited use of builtins.  We run the
  benchmarks, subtract the total time for builtin execution as
  predicted by the builtin cost model, and divide the remaining time
  by the number of basic machine steps executed to arrive at an
  average time for each machine step (see the earlier discussion).
  This is then stored in another JSON file,
  [`plutus-core/cost-model/data/cekMachineCosts.json`](./data/cekMachineCosts.json).
  This cost is currently the same for each step, but more careful
  testing may enable us to produce more precise costs per step at some
  future date.  The JSON file also contains a constant cost for
  machine startup (perhaps a misnomer): this cost is currently very
  small (ideally it would be zero, but that caused difficulties when
  reading the JSON), but experiments hint that there is an element of
  overall execution time which cannot be explained purely by code
  execution. This perhaps depends on the size of the AST or the number
  of unique AST nodes which are visited during program execution, but
  we have not yet been able to pin down precisely what is going on,
  and in any case this effect appears to be relatively small.

*  We can now assign a cost to an arbitrary Plutus Core program by running it
   and adding up the costs for each machine step and for each evaluation of a
   built-in function (as given by the function's cost model applied to the
   argument sizes).  This can be done automatically with `uplc evaluate --counting`
   (see [plutus-core/executables](../../plutus-core/executables)).


## Adding a new built-in function and a suitable costing function

This section describes the somewhat involved process of updating the cost model
when a new built-in function is added to Plutus Core. For concreteness we show
how to add a new builtin `xorByteString` and how to extend the cost model to
cover it.  This is quite a simple example, but serves to illustrate all of the
steps that need to be taken to update the cost model.  For full technical
details of how to add a new built-in function see the extensive notes on "How to
add a built-in function" in
[`PlutusCore.Default.Builtins`](../plutus-core/src/PlutusCore/Default/Builtins.hs).
For documentation on how to add a new built-in type, see
[`Universe.Core`](../plutus-core/src/Universe/Core.hs).  Note that the procedure
described here will only add a new built-in function to Plutus Core: to make a
new function available from Haskell more work will be required in the
[`plutus-tx`](https://github.com/input-output-hk/plutus/tree/master/plutus-tx)
codebase.


### Adding a new function

1. Add a new constructor to the `DefaultFun` type in
   [`PlutusCore.Default.Builtins`](../plutus-core/src/PlutusCore/Default/Builtins.hs). In
   our example we will call this constructor `XorByteString`.  The functions in
   `DefaultFun` become accessible from Plutus Core via names obtained by
   converting the first character of their name to lower case, so in textual
   Plutus core our function will be called `xorByteString`.

2. Add a clause for the new function in the instances for `ToBuiltinMeaning` in
  [`PlutusCore.Default.Builtins`](../plutus-core/src/PlutusCore/Default/Builtins.hs):

    ```
    toBuiltinMeaning XorByteString =
        makeBuiltinMeaning
            xorByteString
            mempty
            where xorByteString a b =
                      Data.ByteString.pack $ zipWith (Data.Bits.xor) (Data.ByteString.unpack a) (Data.ByteString.unpack b)
    ```

    This assumes that the appropriate modules have been imported.  The
    implementation is arguably incorrect since if the arguments have different
    lengths the trailing bytes in the longer argument will be ignored, but it
    serves to illustrate the process; a more robust implementation might perform
    a check that the inputs are the same length.  For more complicated functions
    one might also put the implementation in a separate file.

    The final argument of `makeBuiltinMeaning` contains the costing functions for
    the relevant builtin.  Initially this should be set to `mempty`; we'll come
    back and fix it later.

    Note that there are certain restrictions on built-in functions: for example,
    the function should be deterministic, it **must not throw any exceptions**,
    and ideally it should be easy to cost (the execution time should depend on
    the sizes of the arguments in some fairly straightforward way).

3. Add an integer tag for the new function to the `encode` and
`decode` methods in `instance Flat DefaultFun` in the same file.  This
determines how the new builtin is encoded in the `Flat` serialisation
format: it should be different from all the existing tags and should
be less than 128; typically you should use the smallest unused number.
The existing tags **must not be changed** since changing them would
prevent existing scripts from being decoded properly.

4. The new builtin should now  automatically become available in Plutus Core.

5. Further work will be required to make the builtin accessible from Haskell.
See [`PlutusTx.Builtins`](../../plutus-tx/src/PlutusTx/Builtins.hs) for examples
of how this is done.

6. You may want to add some tests in
[`Evaluation.Builtins.Definition`](../untyped-plutus-core/test/Evaluation/Builtins/Definition.hs)
to check that the semantics of the new builtin are correct.

### Adding the costing functions for a new built-in function

After the above steps have been carried out the new builtin will be available in
Plutus Core, but will not incur any charges when it is called.  To fix this we
have to add a costing function of a suitable shape and replace the `mempty` in
the definition of the function.

#### Step 1: add the basic type of the costing function to the cost model type 

Firstly, add a new entry to the `BuiltinCostModelBase` type in
[`PlutusCore.Evaluation.Machine.BuiltinCostModel`](../plutus-core/src/PlutusCore/Evaluation/Machine/BuiltinCostModel.hs).
For example

```
    paramXorByteString :: f ModelTwoArguments
```

The types of costing functions are defined in
[`PlutusCore.Evaluation.Machine.CostingFun.Core`](../plutus-core/src/PlutusCore/Evaluation/Machine/CostingFun/Core.hs).
There are types `ModelOneArgument`, `ModelTwoArguments`,
`ModelThreeArguments`, `ModelFourArguments`, `ModelFiveArguments`, and
`ModelSixArguments`: each of these types has a number of constructors
describing different forms of costing function for functions with the
appropriate number of functions.  The existing costing function types should
suffice in most situations, but new constructors can be added if necessary:
in this case you should add new cases to the appropriate
`run<N>ArgumentModel` and `runCostingFunction<N>Arguments` functions.

For `xorByteString` it would be reasonable to expect the time taken to be linear
in the minimum of the argument sizes (the function stops when it gets to the end
of the smaller bytestring), so we should use the `ModelTwoArgumentsMinSize`
constructor: see Step 6 for this, and Step 7 for a caveat.


#### Step 2: add a unit cost model for new function

Add a new entry in `unitCostBuiltinCostModel` in
[`PlutusCore.Evaluation.Machine.ExBudgetingDefaults`](../plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs)
(this is used by the `uplc` command for counting the number of times
each builtin is called during script execution, which can useful for
diagnostic purposes).  It should be clear how to do this.  For the
`xorByteString` function we add

```
    , paramXorByteString                   = unitCostTwoArguments
```

#### Step 3: add an outline costing function entry in the JSON file

Add a new entry in [`builtinCostModel.json`](./data/builtinCostModel.json):

```
    "xorByteString": {
        "cpu": {
            "arguments": {
                "intercept": 0,
                "slope": 0
            },
            "type": "min_size"
        },
        "memory": {
            "arguments": {
                "intercept": 0,
                "slope": 0
            },
            "type": "min_size"
        }
    }
```

The coefficients here are unimportant at the moment so we set them all to zero:
Correct figures will be filled in later based on benchmarking results, but we
need to add the basic form of the costing functions first to avoid a circularity
problem: see the Note "Modifying the Cost Model" in
[`PlutusCore.Evaluation.Machine.ExBudgetingDefaults`](../plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs).

The JSON keys are obtained automatically from the types in
[`PlutusCore.Evaluation.Machine.CostingFun.Core`](../plutus-core/src/PlutusCore/Evaluation/Machine/CostingFun/Core.hs)
by the code in `PlutusCore.Evaluation.Machine.CostingFun.JSON`.  In
our case, the costing function is given by the
`ModelTwoArgumentsMinSize` constructor of the `ModelTwoArguments`
type. The type prefix `ModelTwoArguments` is removed from the
constructor name and the remaining `MinSize` is converted to
`min_size` by the Aeson library's
[`CamelToSnake`](https://hackage.haskell.org/package/deriving-aeson-0.2.8/docs/Deriving-Aeson.html#t:CamelToSnake)
transformation.  Similarly, the names of the
`modelMinSizeIntercept` and `modelMinSizeSlope` fields in the
`ModelMinSize` type are converted to `slope` and `intercept`.  In
many cases you should be able to see what the JSON should look like by
looking at existing entries in
[`builtinCostModel.json`](./data/builtinCostModel.json), but in case
of difficulty try the alternative method mentioned in the "Modifying
the Cost Model" note.


#### Step 4: add the correct costing function to the definition of the new builtin

Now go back to
[`Builtins.hs`](../plutus-core/src/PlutusCore/Default/Builtins.hs) and
replace `mempty` in the definition of the builtin with some code to
run the appropriate `param<builtin-name>` function:

```
    toBuiltinMeaning XorByteString =
        makeBuiltinMeaning
            xorByteString
            (runCostingFunTwoArguments . paramXorByteString)
            where xorByteString a b =
                      Data.ByteString.pack $ zipWith (Data.Bits.xor) (Data.ByteString.unpack a) (Data.ByteString.unpack b)
```

#### Step 5: add a benchmark for the new builtin and run it

Now a CPU usage benchmark for the function will have to be added in
[`plutus-core/cost-model/budgeting-bench`](./budgeting-bench) and new R code
will have to be added in [`models.R`](./data/models.R) to process the results of
the benchmark (see Step 6 below).  The benchmark should aim to cover a wide
range of inputs in order to get a good idea of the worst-case behaviour of the
function: experimentation may be needed to achieve this.

Once the benchmark is in its final form, run it using `cabal run
plutus-core:cost-model-budgeting-bench -- --csv <file>` as described in the
first section of this document. Either run the full set of benchmarks and save
the full output in a CSV file or run the new benchmark alone using `cabal run
plutus-core:cost-model-budgeting-bench -- --csv <file> <benchmark name>` to run
the benchmark on its own and then add the output in `<file>` results to a CSV
file (such as `benching.csv`) containing earlier benchmark results for the rest
of the builtin functions.  If the latter method (which will be much faster) is
used it is advisable to run some other costing benchmarks as well to check that
the results are at least approximately consistent with the previous ones.


#### Step 6: update the R code

We now have to extend the R code in [`models.R`](./data/models.R).  Firstly, add
an entry for the arity of the builtin in the `arity` function:

```
   arity <- function(name) {
       switch (name,
           "AddInteger" = 2,
           ...
           "XorByteString" = 2,
           ...
           )
```

Now add a function to infer coefficients for the CPU costing function from
benchmarking data. The exact form of the R code will depend on the behaviour of
the function being added and will probably be based on the expected time
complexity of the function, backed up by examination of the initial benchmark
results. In simpler cases it may be possible to re-use existing R code, but
sometimes more complex code may be required to obtain a good model of the
behaviour of the function. Ideally the R model should accurate over a wide range
of inputs so that charges for "typical" inputs are reasonable but worst-case
inputs which require large computation times incur large charges which penalise
excessive computation. Developing the model may involve some experimentation,
and it may not always be possible to satisfy both goals simultaneously. In such
cases it may be necessary to sacrifice some accuracy in order to guarantee
security.


In the case of `xorByteString` we assume that the time taken will be linear in
the minimum of the sizes of the arguments (ie, the arguments of the new
builtin).  It is often worthwhile to plot the benchmark data and experiment with
it in order to check that it has the form expected when the basic shape of the
costing function was selected (Steps 1, 3 and 6).  For example, we have assumed
that the execution time of `xorByteString` is linear in the _minimum_ of the
argument sizes since the function stops when it gets to the end of the smaller
argument, but note that we call `unpack` on both arguments and that this takes
linear time. Examination of benchmark results might reveal that if one input is
very large then the unpacking step will dominate the execution time, and if this
is the case it might be more sensible to use a model linear in the _maximum_ of
the input sizes.  In general, think carefully about the structure of the model
and issues such as whether the raw data might need to have outliers discarded or
whether only some subset of the data should be used to arrive at an accurate
worst-case model.

```
    xorByteStringModel <- {
        fname <- "XorByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ pmin(x_mem, y_mem), filtered)
        adjustModel(m,fname)
    }
```

Finally, add an entry to the list which is returned by `modelFun` (at the very
end of the file):

```
        xorByteStringModel = xorByteStringModel,
```

From the point of view of Haskell this effectively creates a record field called
`xorByteStringModel` which contains a Haskell representation of the R model
object. (That's what gets read in by the code in Step 6: `paramXorByteString`
contains the string "xorByteStringModel" and that lets the Haskell code retrieve
the correct thing from R.)

#### Step 7: add code to read the costing function from R into Haskell 

Next we have to update the code which converts benchmarking results into JSON
models.  Go to
[`CreateBuiltinCostModel`](./create-cost-model/CreateBuiltinCostModel.hs) and add
entries for the new builtin in builtinCostModelNames

```
  , paramXorByteString                   = "xorByteStringModel"
```
(Getting the string wrong here, for example putting "xorByteString" instead will
give `parse error (not enough input) at ""`. Errors will occur whenever the
Haskell code attempts to read something from an R object that doesn't actually
occur in the object, and they can sometimes be quite cryptic.)

Also add a new clause in [`CreateBuiltinCostModel`](./create-cost-model/CreateBuiltinCostModel.hs):

```
    paramXorByteString                   <- getParams xorByteString paramXorByteString
```

and a function to extract the cost parameters for the R code.  This should be modelled on the existing
functions at the end of the file:

```
xorByteString :: MonadR m => (SomeSEXP (Region m)) -> m (CostingFun ModelTwoArguments)
xorByteString cpuModelR = do
  cpuModel <- ModelTwoArgumentsMinSize <$> readModelMinSize cpuModelR
  let memModel = ModelTwoArgumentsMinSize $ ModelMinSize 0 1
  pure $ CostingFun (cpuModel) memModel
```

The CPU costing function is obtained by running the R code, but the memory usage
costing function is defined statically here.  Memory usage costing functions
only account for memory retained after the function has returned and not for any
working memory that may be allocated during its execution.  Typically this means
that the memory costing function should measure the size of the object returned
by the builtin.  For our `xorByteString` implementation, if the arguments have
sizes `m` and `n` then the result will have size `min(m,n)` so we define the memory
costing function to be `(m,n) -> 0 + 1*min(m,n)`.


#### Step 8: test the Haskell versions of the costing functions

The code in [`CreateCostModel`](./create-cost-model/CreateBuiltinCostModel.hs)
converts the cost modelling functions fitted by R into Haskell functions.  As
mentioned in the [first section](#updating-an-existing-cost-model), there are
tests in
[`plutus-core/cost-model/test/TestCostModels.hs`](./test/TestCostModels.hs) that
check that the results returned by the Haskell functions (which do calculations
in an integral type) agree with those obtained by running the R code (which does
floating point calculations) to within a reasonable margin of error.  Add a new
case to the `main` function to cover the new builtin (it should be fairly clear
how to do this) and then run the tests with `cabal bench
plutus-core:cost-model-test`.


#### Step 9: update the cost model JSON file

Once the previous steps have been carried out, proceed as described in the first
section: feed the results of the costing benchmarks to `generate-cost-model` to
produce a new JSON cost model file (which will contain sensible coefficients for
the costing functions for the new builtin in place of the arbitray ones we added
in Step 3), and check it in along with a CSV file containing a full set of
benchmark results which can be used to reproduce it.

If you're confident that the evaluator hasn't changed too much since
the cost model was last fully updated it may be possible to save time
by using the `-p` option just to run the benchmark for the new
builtin: the results can then be manually inserted into the CSV file
containing the figures for the other builtins.  If you do this then
you may wish to re-run some subset of the benchmarks to check that
things haven't changed too much.

(In future we hope to make this process easier to carry out, and
perhaps also to provide some mechanism to allow external contributors
can run benchmarks on their own machine and have the results re-scaled
to be compatible with our reference machine, thereby removing (or at
least lessening) the necessity for Cardano developers to do the
benchmarking).
