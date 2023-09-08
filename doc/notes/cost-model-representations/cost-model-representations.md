# Representations of the Plutus Core cost model

The `plutus` codebase uses several different representations of the Plutus Core
cost model.  It can be somewhat difficult to keep track of what all of these are
used for; this document attempts to give an overview to clarify matters.  An
essential point is that if you're using `mkEvaluationContext` then cost model
parameters much be provided in the correct order, otherwise script costs
will be inaccurate: see [`EvaluationContext`](#evaluationcontext) below.

## Introduction

The Plutus Core language incorporates a _cost model_ which assigns costs for CPU
usage and memory usage to the evaluation of an Untyped Plutus Core program on
the standard Plutus evaluator (the _CEK machine_).  CPU costs are measured in
abstract units called `ExUnit`s (_execution units_), with one `ExUnit`
corresponding to one picosecond on a specific dedicated benchmarking machine.
We expect that that the actual time required to execute a program on some other
machine will be (approximately) proportional to the total number of `ExUnit`s.

Memory usage, or "size", is measured in units of 64-bit words (although with
hindsight the number of bytes required to store an object might have been a
better measure).

The cost model consists of two components:

  1. A CPU and memory cost for every basic step of the evaluator. 
  2. A pair of _costing functions_ for each built-in function which give an
     approximation to the CPU usage and memory usage of the function.  The cost
     generally depends on the size of the input(s) to the builtin, which is why
     we need a function rather than just a constant.  The CPU costing functions are
     determined by running benchmarks and fitting regression models to the
     results.  The memory costs of a built-in function (which measure only the
     memory required to store the output of the function, and not any transient
     memory allocated during execution) are determined by understanding what the
     builtin does, and perhaps by examining the implementation.

### Serialised representation

Concrete values for the coefficients of the costing functions for the builtins
in the current version of Plutus Core are stored in the file
[`builtinCostModel.json`](https://github.com/input-output-hk/plutus/blob/master/plutus-core/cost-model/data/builtinCostModel.json)
and values for the machine steps are stored in
[`cekMachineCosts.json`](https://github.com/input-output-hk/plutus/blob/master/plutus-core/cost-model/data/cekMachineCosts.json
) (both in `plutus-core/cost-model/data`). Note that these are not necessarily
the values in use on the chain at any given time.  The definitive values used
for calculating on-chain costs are protocol parameters which are part of the
state of the chain: in practice these will usually have been obtained from the
contents of the JSON files at some point in the past, but we do not guarantee
this.  See [below](#evaluating-scripts-on-the-chain) for more details of how the
on-chain cost model parameters are passed to the Plutus Core evaluator.

For example, the costing functions for `lessThanEqualsByteString` are
represented by the following entry, which says that the CPU cost of comparing
two bytestrings `r` and `s` is `156 + 197145 * min {size(r), size(s)}`
(reflecting the fact that in the worst case you have to scan the whole of the
shorter of the two strings before you can tell whether one is less than the
other), and the memory cost is 1 (required to store the boolean result of the
comparison).

    "lessThanEqualsByteString": {
        "cpu": {
            "arguments": {
                "intercept": 197145,
                "slope": 156
            },
            "type": "min_size"
        },
        "memory": {
            "arguments": 1,
            "type": "constant_cost"
        }
    }

We refer to the numbers in this structure as the _cost model parameters_.


### Internal Haskell representations
There are a number of different Haskell representations of these structures in the Plutus codebase,
and it can be difficult to work out which ones are used where.

#### The main representation

The main internal representation of the cost model is given by the
[BuiltinCostModelBase](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/BuiltinCostModel.hs#L70)
type, which is a record type with one field for each built-in function. The type
is parametric over a type `f`.  In reality we instantiate `f` to be the
`CostingFun` type defined
[here](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/CostingFun/Core.hs#L75)
to obtain the [BuiltinCostModel](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/BuiltinCostModel.hs#L57) type.

When the UPLC evaluator is compiled the contents of `builtinCostModel.json` are
read in and converted into a BuiltinCostModel object called
[defaultBuiltinCostModel](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs#L36).
The costs for the different types of CEK steps (all of which currently have the
same cost) are defined in
[cekMachineCosts.json](https://github.com/input-output-hk/plutus/blob/master/plutus-core/cost-model/data/cekMachineCosts.json)
which is compiled into a CekMachineCosts object called [defaultCekMachineCosts](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs#L65),
and this is bundled together with the builtin costs in [defaultCekCostModel](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExBudgetingDefaults.hs#L69) (of
type [CostModel CekMachineCosts BuiltinCostModel](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/MachineParameters.hs#L28)).

#### Flattened cost model entries

The hierarchical structure described above is a natural representation for use
within `PlutusCore`, but for interoperating with other sources of cost model
parameters (the ledger, for example) it is sometimes more convenient to use a
flattened representation consisting of a list of pairs of (key, value) entries
or a map from keys to values containing entries like

```
("lessThanEqualsByteString-cpu-arguments-intercept", 197145)
("lessThanEqualsByteString-cpu-arguments-slope", 156)
("lessThanEqualsByteString-memory-arguments", 1)
```

In particular, the type `CostModelParams = Map.Map Text.Text Integer` (defined
[here](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/CostModelInterface.hs#L147)
in `PlutusCore.Evaluation.Machine.CostModelInterface`) uses this format.  The
[applyCostModelParameters](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/CostModelInterface.hs#L273)
function in the same file takes a `CostModelParams` object `p` and a CostModel `c`
and updates the costing functions in `c` with the values from `p`.  Any entries
in `c` which are not mentioned in `p` are left unaltered, but if `p` contains an
entry which does not already exist in `c` then an error occurs.

The flattened representation merges both components of the cost model (the
evaluator step costs and the builtin costs) into a single list.

See also the Notes at the top of
[CostModelInterface.hs](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/CostModelInterface.hs).


#### MachineParameters

The [MachineParameters](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/MachineParameters.hs#L39) type bundles together a cost model and the denotations of
the builtins, and this is used by the machinery which evaluates builtins to both
evaluate a call to a builtin and cost it.  It's generic over a type `fun` which
describes the built-in functions.  For testing,  the `MachineParameters` object
that we use is `defaultCekParameters`, where `fun` is
[DefaultFun](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs#L53),
the big list that includes all of the functions in all versions; `defaultCekParameters` is built from
the contents of the JSON files described [earlier](#serialised-representation).

The function
[mkMachineParametersFor](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/MachineParameters/Default.hs#L42)
in `PlutusCore.Evaluation.Machine.MachineParameters.Default` creates a set of
machine parameters from a
[BuiltinSemanticsVariant](https://github.com/input-output-hk/plutus/blob/3617b1f318c1af25202b3ecec098ce18d3b7c875/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs#L1056)
which selects which implementation of each builtin is used (implementations can
change as time progresses, but old implementations must be retained to allow old
scripts to be validated), and a list of cost model parameters which is used to
update the constants in `defaultCekCostModel` with new values.


## The cost model and the ledger

The ledger also has to deal with cost models, but it uses different
representations from those in `plutus-core`.  The situation is complicated by
the fact that the ledger has to keep track of different versions of the cost
model.  New entries may be added to the cost model for new builtins, and entries
for existing builtins may change for a number of reasons (for example a changed
implementation); however, previous versions of the cost model must be retained
in order to allow old scripts to be validated when the history of the chain is
replayed.  Also, new features may be added to the evaluator as it evolves and
costs will have to be added for them.  The precise set of builtins available at
a given time(among other things) is determined by some metadata (the "ledger
language") attached to on-chain scripts: ledger language tags are currently of
the form `PlutusV1`, `PlutusV2`, and so on.  See
[CIP-35](https://cips.cardano.org/cips/cip35/) for a more detailed discussion of
various versions used in Cardano.

The ledger interacts with the Plutus Core evaluator using functions defined in
[plutus-ledger-api](https://github.com/input-output-hk/plutus/tree/master/plutus-ledger-api).
The provides functions
[evaluateScriptCounting](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-ledger-api/src/PlutusLedgerApi/V1.hs#L158)
and
[evaluateScriptRestricting](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-ledger-api/src/PlutusLedgerApi/V1.hs#L173)
(there are PlutusV2 and PlutusV3 versions of these too) to run scripts on the
Plutus Core evaluator with a particular cost model.  These functions take an
argument of type
[EvaluationContext](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-ledger-api/src/PlutusLedgerApi/Common/Eval.hs#L116),
which contains all of the static parameters that the evaluator needs to evaluate
a script, including a cost model.  

#### `EvaluationContext`

The
[EvaluationContext](https://github.com/input-output-hk/plutus/blob/b321575d9266b3358b9e728d064fc0bee4f355d7/plutus-ledger-api/src/PlutusLedgerApi/Common/Eval.hs#L116)
type is defined in `plutus-ledger-api`, in `PlutusLedgerApi.Common.Eval`, and is
the part of the interface that the ledger uses to interact with the Plutus Core
evaluator.  `EvaluationContext` objects are created using the
[mkEvaluationContext](https://github.com/input-output-hk/plutus/blob/e773e58ea0e4a8088fed0ea5f934a7c413caa5b3/plutus-ledger-api/src/PlutusLedgerApi/V1/EvaluationContext.hs#L28)
function in `PlutusLedgerApi.V{1,2,3}.EvaluationContext` (which in turn uses
`mkMachineParametersFor`, described earlier). The required cost model is
supplied in the form of a list of integers giving the cost model parameters in
the same order as the flattened form of the cost model described
[above](#flattened-cost-model-entries).  It is **ESSENTIAL** that the correct
number of cost model parameters are supplied and that they are given in the
correct order: if not, the costs of scripts will be completely inaccurate.

The cost model parameters can be re-ordered between ledger language versions
(PlutusV1, PlutusV2, ...) but new builtins can also be added without a new
ledger language version, and in this case any new parameters must be added at
the end of the list.

## Evaluating scripts on the chain

The ledger stores a cost model as a [list of `Integer`
values](https://github.com/input-output-hk/cardano-ledger/blob/330b42db03fec425ad72c98cb6931f979e59941b/eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Scripts.hs#L330)
which is converted to an `EvaluationContext` using `mkEvaluationContext`, the
resulting being used by `evaluateScriptCounting` and `evaluateScriptRestricting`.

The cost model parameters are stored on the chain as protocol parameters, which
in principle can be updated at almost any time.

When a script is evaluated on the chain, the cost model parameters (for the
Plutus ledger version associated with the script) in the current protocol
parameters are used.  When the history of the chain is replayed the same
protocol parameters will be used, so the cost will be the same.  However, the
cost model parameters for any version can be changed in any update of the
protocol parameters, so the cost of a fixed script may vary according on when it
is evaluated.  We haven't yet changed the cost model parameters for any PLC
version after they've first been deployed, but we may do this in the future
(with a theoretical risk that if we increase costs, a particular script which
has run successfully in the past may become too expensive to run within the
node's budget limits).



