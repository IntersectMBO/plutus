# Cardano Constitution script

A cardano constitution script is a plutus function (validator)
that takes as input an empty redeemer (`Unit`) as well as the `V3.ScriptContext` and

1) extracts from `V3.ScriptContext` all the proposed changes to the protocol parameters (of the current proposal under validation)
2) validates that all proposed changes meet the *restrictions* of the constitution.
If any change fails on a single restriction, then the whole proposal fails.

## Configuring the script

To make easier the modification of the constitution script in the future, we made the script configurable by
allowing to specify new restrictions or alter the current restrictions by means of a `ConfigurationConfig`.

This means that to obtain a new constitution script, you must first provide a `ConstitutionConfig`.

``` haskell
constitutionValidator :: ConstitutionConfig -> ConstitutionValidator
```

The current, default configuration is written in json at `data/defaultConstitution.json`, which is then statically read into Haskell
as a value of the `ConstitutionConfig` ADT.

You can take a look at the json schema `data/defaultConstitution.schema.json` for the configuration format and some examples.
The schema is not currently enforced (by some json-schema validator).

Sidenote: writing json to configure the script is not required; it can alternatively be done by directly supplying a `ConstitutionConfig` value.
We only use json for our convenience.

## Different implementation flavors

There are 4 styles of ConstitutionValidator implementations, each being a permutation of the 2 following flavors:

### Static vs NonStatic:

The Static flavor is faster compared to the non-static (supposedly, has not been confirmed).
At compile time (statically), the restriction values of the configuration (e.g. minValue, maxValue)
are turned from plain Integers into predicate functions which will be checked directly at runtime.

The downside of the static flavor is that the user cannot supply an **arbitrary** Configuration
(by means of `PlutusTx.liftCode`), whereas with the non-static this is possible.

### Sorted vs Unsorted:

The Sorted flavor contains an algorithmically faster check of restrictions. It does so by traversing *pair-wise* the changed parameters
together with the configuration config.

For this to work, both the changed parameters and the configuration config must be sorted.

The configuration config is in our control so it is already pre-sorted --- either at compile-time by reading it from JSON, or at run-time by
requiring to be supplied as a `PlutusTx.SortedMap` (type-checking will enforce that).

On the other hand, the changed parameters is not in our control and comes from the ledger as a (potentially) unsorted `PlutusTx.AssocMap`.
We first sort the changed parameters into a `PlutusTx.SortedMap` and then proceed with the pair-wise traversal algorithm.

Another option would be to talk with the `cardano-ledger` Team and agree to switch the changed parameters from an `AssocMap` to a `SortedMap`, plus
enforcing the sortedness validity (see `PlutusTx.SortedMap.isValid`) during BuiltinData deserialization.

### Empty changed parameters issue

Another matter that needs to be discussed with the `cardano-ledger` team is what happens with an empty change of parameters.
Currently, *all 4 implementations* will accept (not fail) on such an "empty" proposal.
The issue is not with costing: the proposal-initiator/user
will be accounted for the cost of the execution of the constitution script, as normal.
There may be an issue by later voting on such an empty proposal: seems redundant (or even worse?).
