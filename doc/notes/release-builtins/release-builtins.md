# Enabling new Plutus Core builtins in `plutus-ledger-api`

The process of releasing new builtins (or other Plutus Core features such as new
AST nodes, like `constr` and `case`) is quite complex and has to take place in
several stages.

1. We add new builtins to the Plutus codebase and test and cost them, and
eventually merge the code with the main branch. At this point the new builtins
are available for use locally via eg `uplc` or Plinth.

2. We also have to expose them to the ledger by adding code in
`plutus-ledger-api`.  This process will be described in greater detail later.

3. Eventually a Plutus release including the new builtins will be integrated
   with the Cardano node, and at some point a new version of the node software will
   be released for public use and will be adopted by node operators.  It may take
   some time until a majority of the nodes in the network are using the new
   software, and until that happens it must be impossible to run scripts which use
   the new builtins on the network since nodes may disagree about the validity of
   scripts. Once a majority of nodes are using the updated software a hard fork
   will take place and at that point it will in principle become possible to use
   the new builtins.  There are two factors which determine whether it's possible to
   use them:

    * During script deserialisation there's a check (see later) which checks if a
      builtin is allowed based on the (major) Protocol Version, which is incremented
      during the hard fork.  If an invalid builtin is found then there will be a
      Phase 1 error and the script will not be executed and will not be stored on
      the chain.

    * If the script deserialises correctly then it will be executed, and any uses of
      a builtin will be charged for as usual, based on the cost model parameters in
      the protocol parameters; however, it's possible that the cost model parameters
      may not contain an entry for a particular builtin, and if this happens then
      the charge for that builtin will be set to the maximum possible, and if the
      builtin is used then the script budget will be exhausted immediately, causing
      a Phase 2 error.

Thus two things have to happen before a builtin becomes usable:

  * A: a protocol parameter update has to happen which updates the cost model
     parameters with costs for the builtin.

  * B: a hard fork has to occur which enables the builtin.

Because these events have to be voted upon separately it's not currently
possible to ensure that they happen simultaneously.

If the parameter update happens first (ie, A happens before B) then until the
hard fork, scripts using the new builtin(s) will fail during Phase 1 validation;
when the hard fork happens such scripts will immediately pass both Phase 1 and
Phase 2 validation.

If the hard fork happens before the parameter update (ie, B happens before A)
then until the parameter update, scripts using the new builtin(s) will pass the
Phase 1 checks but will fail during execution; after the parameter update they
will succeed.

## Updating `plutus-ledger-api`

When a new buitin is added, the `plutus-ledger-api` code and tests must be
updated to prepare for both A and B.

### Cost model parameters

After a costing function has been determined for a new builtin (see [this
document](https://github.com/IntersectMBO/plutus/blob/master/plutus-core/cost-model/CostModelGeneration.md)),
costing information for the builtin will be stored in the files
`builtinCostModelA.json`, `builtinCostModelB.json`, and `builtinCostModelC.json`
in `plutus-core/cost-model/data`.  Once this has been done it will be possible
(inside the `plutus` repository) to run scripts using the new builtin using the
`uplc` command, and script execution will be correctly costed.  However, before
the builtin can be used on the chain the code in `plutus-ledger-api` must be
updated to make it aware of the parameters determining the relevant costing
function.

#### Example
The current costing function for the `multiplyInteger` builtin is represented
by the following entry in `builtinCostModelC.json`.

```
    "multiplyInteger": {
        "cpu": {
            "arguments": {
                "intercept": 90434,
                "slope": 519
            },
            "type": "multiplied_sizes"
        },
        "memory": {
            "arguments": {
                "intercept": 0,
                "slope": 1
            },
            "type": "added_sizes"
        }
    }
```

This says that the CPU cost of calling `multiplyInteger` with arguments `m` and
`n` is `90434 + 519 * size(m) * size(n)` and the memory cost is `size(m) +
size(n)`, where sizes are measured in units of 8-byte words.  There are similar
entries for all of the other builtins, and also for the basic operations of the
CEK machine (see `cekMachineCosts[ABC].json`).  The Plutus Core cost model
consists of all of this information, and the A/B/C variants account for
differences in costs for different ledger languages (ie, PlutusV1, PlutusV2, and
PlutusV3) and some historic changes in costing functions.  The ledger's view of
the cost model is simply as three lists of numbers (one list for each variant)
stored in the protocol parameters, and there is code in `plutus-ledger-api`
which is used to convert these numbers into our more structured internal
representation.  The numbers are referred to as "cost model parameters".

### Cost model parameter names
Before executing a script the the ledger retrieves the relevant set of cost
model parameters from the protocol parameters and calls code in
`plutus-ledger-api` to update the evaluator's internal representation of the
cost model (and some caching is done to avoid repeated updates).  The update
process involves a flattened representation of the cost model where each parameter
has a name obtained from the JSON structure: for example, the four numbers in
the costing function for `multiplyInteger` are called
`multiplyInteger-cpu-arguments-intercept`,
`multiplyInteger-cpu-arguments-slope`,
`multiplyInteger-memory-arguments-intercept`, and `multiplyInteger-memory-arguments-slope` (see 
[this file](https://github.com/IntersectMBO/plutus/blob/master/doc/notes/cost-model-representations/cost-model-representations.md)
for more on the different cost model representations).

The three modules `PlutusLedgerAPI.V[123].ParamName` define `ParamName` types
which enumerate the cost model parameter names for each Plutus ledger language.
These have one constructor for each cost model parameter, and the names of the
constructors are obtained from the flattened cost model parameter names by capitalising
the first letter of the name and replacting all occurrences of `-` by `'`.  Thus the
parameter names for `multiplyInteger` are represented by the following constructors

```
  | MultiplyInteger'cpu'arguments'intercept
  | MultiplyInteger'cpu'arguments'slope
  | MultiplyInteger'memory'arguments'intercept
  | MultiplyInteger'memory'arguments'slope
```

Before a new builtin can be enabled on the chain the `ParamName` types must be
updated by adding constructors for the parameter names for the costing functions
for the new builtin **at the end** of the `ParamName` type.  Do **NOT** change
the order of the existing constructors or add any new entries in the middle.
The order of new cost model parameters doesn't matter, but it's easiest to add
them in the order in which they appear in the JSON files.

Note that we don't add the actual values of the parameters, which are instead
obtained from the ledger via the protocol parameters.  Values for new cost model
parameters must be added to the protocol parameters during a parameter update,
and after the parameter names have been added to the `ParamName` types a
representation of the cost model parameters suitable for the parameter update
can be obtained using the `dump-cost-model-parameters` executable.  See the
`--help` option for information about available output formats; the default
`--json` option should usually be used.

#### Tests
After extending the `ParamName` types also update the "length" tests in
`Spec.CostModelParams` and `Spec.Data.CostModelParams` to use the new numbers of
constructors in the `ParamName` types.

### Available builtins and Plutus Core language versions

Builtins are introduced in batches and each batch is enabled on the chain at a
hard fork (equivalent to a new major protocol version (PV)).  We have also
introduced different Plutus Code ledge languages (or LLs: these are currently
PlutusV1, PlutusV2, and PlutusV3) at various hard forks and up to and including
PV10 it was only possible to enable new builtins for the most recent ledger
language: for example the `verifyEcdsaSecp256k1Signature` function was
introduced in PlutusV2 at PV8 and also became available in PlutusV3 when that
was introduced at PV9, but at the time of writing (PV10) it has never been
available in PlutusV1.  This situation has led to a rather complicated system of
checks for which builtins are available in which (LL,PV) combinations.

Fortunately, from PV11 onwards all builtins will become available in all Plutus
ledger languages, and this simplifies the process of adding new builtins to the
availability check (remember that this is required to account for the fact that
at a given time different nodes may be running different versions of the node
software, which may have different builtins available).

The on-chain builtin availability check is performed by the
`builtinsAvailableIn` function in `PlutusLedgerApi.Common.Versions`.  This makes
use of lists defined in the same module which contain the different batches of
builtins .  Once a batch of builtins has been released, the corresponding list
must **NOT** subsequently be altered in any way.

When new builtins are added to Plutus Core but we don't yet intend to release
them, add them to a new batch (say `batch<N>`) and associate them with
`futurePV` in all Plutus ledger languages in the function `builtinsIntroducedIn`
in `PlutusLedgerApi.Common.Version`.  More builtins can be added to this batch
until we get to the point where we're preparing to release the entire batch.

When we get to the point where we intend to release a new batch of builtins in
an approaching hard fork, do the following:
  * Add a variable corresponding to the new PV, for example `somethingPV`, in `PlutusLedgerApi.Common.ProtocolVersions`.
  * Update `newestPV` to be equal to `somethingPV`.
  * Also update `knownPVs` to include `somethingPV`.
  * Update `builtinsIntroducedIn` say that `batch<N>` will be available in `somethingPV`.
  * Update the tests in `Spec.Versions` and `Spec.Data.Versions` to include the
    names of the new builtins in the `testPermittedBuiltins` functions.

It is possible that we may have added a number of new builtins to Plutus Core
but decide to enable only some subset at the next hard fork.  In this case,
create a new batch `batch<N+1>`, move the builtins aren't to be released into it
and and associate `batch<N+1>` with `futurePV` in `builtinsIntroducedIn`. Leave
the builtins which we _do_ plan to release in `batch<N>` and proceed as above.
Also make sure that the constructors for the builtins in `batch<N>` come before
the ones for `batch<N+1>` in the `ParamNames` types: this may require
re-ordering the constructors (but **NOT** the ones for batches before
`batch<N>`).

**DO NOT** change `testBuiltinAvailabilityCompatibility` in `Spec.Versions` and
`Spec.Data.Versions`.  This checks that old and new versions of
builtinsAvailableIn agree up to the Plomin hard fork (the start of PV10) and it
should never need to be changed in future.

There are also some tests in `PlutusLedgerApi.Test.V3.EvaluationContext` that
probably don't make sense any more and if nothing goes wrong it's probably safe
to ignore them.  These will be reworked or removed at a later date.
