<h1 align="center">Constitution Script</h1>

The overall purpose of a "Constitution Script" is to define
in Plutus, that part of the *Cardano Constitution* which is possible to
be automated as a smart contract.

Currently, in this repository, we are focusing on defining a constitution
script to check that a `ParameterChange` proposal or `TreasuryWithdrawals` proposal
is "constitutional". In the future, we may
enhance the script to automate more parts of the *Cardano Constitution*.

The script is written in the high-level `PlutusTx` language, which
is subsequently compiled to `Untyped Plutus Core` and executed
on then chain upon every new Governance Proposal.

Being a smart contract, the constitution script is a validator function of the form:

``` haskell
const_script :: BuiltinData -> BuiltinUnit
```

The sole argument to this function is the `BuiltinData`-encoded `V3.ScriptContext`.
Note the absence of the 2 extra arguments, previously known as `Datum` argument and the `Redeemer` argument.
Since V3 and CIP-69, the `Datum` and `Redeemer` values are not passed anymore as separate function arguments,
but embedded inside the `V3.ScriptContext` argument.
The "proposal under investigation" is also embedded inside the `ScriptContext`.

`Datum` is not provided for the "constitution script", since it is not a spending validator.
`Redeemer` will be provided to the "constitution script", but the current script
implementations ignore any value given to it (see Clause D).

When the script is fully applied, one of the 2 cases can happen:

1. The script executes successfully by returning `BuiltinUnit`, which means that the Proposal under investigation is
*constitutional* (the next step of the process would be to vote on this proposal, but this is out-of-scope of this repository).

2. The script fails with an error. There can be many different reasons for a script error:

- logical error in the constitution script (in config and/or engine, see next section)
- Proposal is malformed
- Proposal violates a constitution rule.
- bug in the CEK evaluator

Irregardless of the specific error, the outcome is the same: the proposal would be *un-constitutional* (and no further steps will be taken for this proposal).

##  Constitution Rules (a.k.a. GuardRails)

The constitution rules (a.k.a. guardrails) may change in the future, which may require that the constitution script
be also accordingly updated, and re-submitted on the chain so as to be "enacted".

To minimise the chances of introducing bugs when the constititution script has to be updated,
we decided to separate the fixed "logic part" of the script from the
possibly evolving part, i.e. the "constitution rules".
For this reason, the constitution rules are separately given as a `PlutusTx` ADT
(with type `Config`), which when applied to the fixed-logic part (named `engine` for short)
yields the actual constitution script:

``` haskell
data Config = ... -- see Config/Types.hs
const_engine :: Config -> V3.ScriptContext -> BuiltinUnit
const_engine = ...fixed logic...

const_script :: V3.ScriptContext -> BuiltinUnit
const_script = const_engine my_config
```

In other words, the `Config` is "eliminated" statically at compile-time, by partially applying it to
the constitution engine.

These constitution rules can be thought of as predicates (PlutusTx functions that return `Bool`)
over the proposed values. We currently have 3 such predicates:

``` haskell
minValue configValue proposedValue = configValue Tx.=< proposedValue
maxValue configValue proposedValue = configValue Tx.>= proposedValue
notEqual configValue proposedValue = configValue Tx./= proposedValue
```

An alternative & preferred method than constructing a `Config` inside Haskell, is to
edit a configuration file that contains the "constitution rules" laid out in JSON.
Its default location is at `data/defaultConstitution.json`,
with its expected JSON schema specified at `data/defaultConstitution.schema.json`.
After editing this JSON configuration file and re-compiling the cabal package, the JSON will be statically translated
to a `Config` PlutusTx-value and applied to the engine to yield a new script.
This is the preferred method because, first, it does not require any prior PlutusTx/Haskell knowledge
and second, there can be extra sanity checks applied: e.g. when parsing/translating the JSON to `Config`
or when using an external JSON schema validator.

## ChangedParameters Format

In case of a `ParameterChange` governance action, the ledger will construct out of the proposed parameters, a `ChangedParameters` value,
encode it as `BuiltinData`, then pass it onto us (the Constitution script) inside the `V3.ScriptContext`.
This `BuiltinData` object has the following format (in pseudocode):

```
ChangedParametersData = Map ChangedIdData ChangedManyValueData
ChangedIdData = I Integer
ChangedManyValueData =
     ChangedSingleValueData
   | List[ChangedSingleValueData...]
   -- ^ an arbitrary-length, heterogeneous (integer or ratio) list of values (to support sub-parameters)

ChangedSingleValueData =
     I Integer  -- a proposed integer value
   | List[I Integer, I Integer] -- a proposed numerator,denominator (ratio value)
   -- ^ a 2-exact element list; *BE CAREFUL* because this can be alternatively (ambiguously) interpreted
   -- as a many-value data (sub-parameter) of two integer single-value data.
```

, where Map,I,List are the constructors of `PlutusCore.Data`
and `Integer` is the usual arbitrary-precision PlutusTx/Haskell `Integer`.
There is no other type of a changed parameter (e.g. nested-list parameter), so the script implementations will fail on any other format.

## Specification of script implementation

There can be many different implementations of the logic (engine) made for the constitution script.
A particular script implementation behaves correctly (is valid), when it
complies with **all** the following clauses:

### Clauses

- S01. If `thisGovAction` is `TreasuryWithdrawals _ _`, then `PASS` and no checks left.
- S02. If `thisGovAction` is `(ParameterChange _ proposedParams _)` and the decoded `proposedParams` is an empty list (a.k.a. Tx.AssocMap), then `UNSPECIFIED`.
- S03. If `thisGovAction` is `(ParameterChange _ proposedParams _)` and decoded `proposedParams` is a non-empty list,
start checking each proposed parameter in the list against the `Config`.
- S04. The Redeemer `BuiltinData` value is `UNSPECIFIED`.
- S05. In all other cases of decoded `ScriptContext` return `FAIL`.
- S06. Lookup in the `Config` the rules associated to the current `proposedParam`'s id and test these rules against the `proposedParam`'s value. If one or more tests fail => `FAIL`.
Otherwise, set the next `proposedParam` in the list as the current one and continue to (F).
- S07. If no `proposedParam` to check is left in the `proposedParams` list, `PASS` and no more checks left.
- S08. If a `proposedParam`'s id is not found in the `Config` => `FAIL`. This can happen if the parameter is unknown, or is known but wrongfully omitten from the config file.
- S09. If the `Config` says `{type: any}` under a given `proposedParam` , then do not try to decode the value of the `proposedParam`, but simply `PASS` and continue to next check.
- S10. In all other cases of `{type: integer/unit_interval/list}`, decode the `proposedParam` value according to the expected type (see "ChangedParameters Format"). If
the encoding of the `proposedParam` value does not match the expected encoding of that type, `FAIL`.
- S11. In case of expected type `list`, if more or less than the expected length of the list elements are proposed, `FAIL`.

### Legend

- `thisGovAction` : `(fromBuiltinData(v3_context) -> scriptcontextScriptInfo -> (ProposingScript _ (ProposalProcedure _ _ thisGovAction)))`
- `PASS`: An implementation accepts the check, and continues with the rest of the checks.
If there are no checks left, the script returns `BuiltinUnit`, thus deeming this proposal constitutional.
- `FAIL`: An implementation must make the overall script fail with an error (explicitly by calling `Tx.error ()` or implicitly e.g. `1/0`), thus deeming the proposal un-constitutional.
- `UNSPECIFIED`: The behavior is explicitly left unspecified, meaning that
implementations may decide to `PASS` or `FAIL` or loop indefinitely --- note that in reality, looping indefinitely
behaves the same as `FAIL` since plutus scripts are "guarded" by certain resource limits.

### Ledger guarantees

Although not part of the specification, the
ledger provides us extra **guarantees**, which a valid implementation may optionally
rely upon (i.e. take it as an assumption):

- G01. The underlying AssocMap does not contain duplicate-key entries.
- G02. The underlying AssocMap is sorted on the keys (the usual Ordering Integer).
- G03. The underlying AssocMap is not empty.
- G04. Unit_Interval's denominator is strictly positive.
- G05. Unit_Interval's numerator and denominator are co-prime.
- G06. Unit_Interval's value range is [0,1] (i.e. both sides inclusive).
- G07. Protocol parameter IDs are positive.
- G08. Redeemer is encoded as `()`.
FIXME: any governance proposal?

## Current script implementations

There are 2 engine implementations:

- `Unsorted`
- `Sorted`

`Unsorted` and `Sorted` must be valid implementations, so they must comply to all clauses [S01..].

`Unsorted` does not rely on any ledger guarantees.
`Sorted` as the name implies relies on sortedness to work and thus assumes the G01,G02 guarantees.
`Sorted` further requires that the `Config` is also sorted, which must be guaranteed **by-construction** when using the JSON `Config` format
(this is not currently guaranteed when manually constructing a `Config` ADT value).

Note that, although all implementations could theoretically work without problem with negative `proposedParam` ids,
the `Config` JSON format (not the ADT) and the Ledger are limited only to positive ids (see G07).

The **Sorted** implementation is the selected implementation to be used on the mainnet chain.

## Testing the implementations

The testing infrastructure generates artificial proposals and unit/random tests them
against the 2 valid implementations, unsorted and sorted.

The artificial proposals are built such as to satisfy all specification clauses `[S01..]` (required for validity).

Since this repository's testing infrastructure cannot be aware or test the ledger's behavior,
we have to make explicit the ledger guarantees  that the test code needs to rely upon.
To keep things simple and uniform, we decided that the (random) testing infrastructure has to rely on
the union (Sum) of the ledger guarantees required by all our current implementations, i.e. G01,G02.

## Repository layout

- `src/Cardano/Constitution/Config/*` : types and instances for the `Config` ADT
- `src/Cardano/Constitution/Config.hs` : "predicate meanings" and umbrella module for the `Config`
- `src/Cardano/Constitution/Validator/Sorted.hs` : sorted engine
- `src/Cardano/Constitution/Validator/Unsorted.hs` : unsorted engine
- `src/Cardano/Constitution/Validator/Common.hs` : common code between the 2 engines
- `data/*` : contains the JSON configuration files
- `test/*`: testing code
- `app/create-json-envelope`: an executable to construct constitution script, ready to be submitted to the chain

## Building the script

We have created an executable `create-json-envelope` to ease the creation of a constitution script.
This executable is disabled by default; to enable it, uncomment the related lines inside this repo's `cabal.project`:

```
-- Uncomment the following lines to make cardano-constitution:create-json-envelope buildable:True
--
-- package cardano-constitution
--   flags: +force-build
-- allow-newer: *:plutus-ledger-api
-- allow-older: *:nothunks
```

Then,

``` haskell
cabal run cardano-constitution:create-json-envelope -- out.plutus
```

will create `out.plutus` JSON file that contains the plutus code as-configured by `data/defaultConstitution.json`,
ready to submit it to the chain.
Normally any editing of `data/defaultConstitution.json` should be picked up by re-running `cabal run`;
if not, use also `-fforce-recomp`.
