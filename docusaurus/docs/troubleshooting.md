---
sidebar_position: 80
---

# Troubleshooting

## Plugin errors

Errors that start with `GHC Core to PLC plugin` are errors from `plutus-tx-plugin`.

> :pushpin: **NOTE** 
> 
> Often, these errors arise due to GHC doing something to the code before the plugin gets to see it. 
> The solution is often to prevent GHC from doing this. 
> We often recommend trying various GHC compiler flags.

### Haddock

The plugin will typically fail when producing Haddock documentation.
However, in this instance, you can simply tell it to defer any errors to runtime. Since you are only building documentation, runtime errors won't occur. 

To tell the plugin to defer any errors to runtime, add the following lines for your `package-name` to `cabal.project`:

```
package package-name
  haddock-options: "--optghc=-fplugin-opt PlutusTx.Plugin:defer-errors"
```

### Non-`INLINABLE` functions

A common error is:

`Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function`

This means the plugin doesn't have access to implementation of the function, which it needs to be able to compile the function to Plutus Core. 
Some things you can do to fix it:

- Make sure to add `{-# INLINABLE functionname #-}` to your function.
- If there's an extra `$c` in front of the function name in the error, GHC has generated a specialized version of your function, which prevents the plugin from accessing it. You can turn off specialization with `{-# OPTIONS_GHC -fno-specialise #-}`
- Other compiler options that can help:
   - `{-# OPTIONS_GHC -fno-strictness #-}`
   - `{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}`
   - `{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}`
   - `{-# OPTIONS_GHC -fobject-code #-}`

More details are available in [the plutus-tx readme](https://github.com/IntersectMBO/plutus/tree/master/plutus-tx#building-projects-with-plutus-tx).

## Haskell Language Server issues

For more advice on using Haskell Language Server (HLS), consult the [CONTRIBUTING guide](https://github.com/IntersectMBO/plutus/blob/master/CONTRIBUTING.adoc) in the `plutus` repository.

### Wrong version

`ghcide compiled against GHC 8.10.3 but currently using 8.10.2.20201118`

Your editor is not picking up the right version of the Haskell Language Server (HLS). 
Plutus needs a custom version of HLS which is provided by Nix. 
To get this working in your editor, make sure to do these two things:

- Start your editor from `nix develop` (or use `direnv`)
- Most editors are configured to use `haskell-language-server-wrapper`, a wrapper that picks the right HLS version. Change this to: `haskell-language-server`.

If this doesn't work, run `which haskell-language-server` in *nix develop*, and use this absolute path in the configuration of your editor.

## Error codes

To reduce code size, on-chain errors only output codes. 
Here is a list of error code definitions:

### Ledger errors
- `L0: Input constraint`
- `L1: Output constraint`
- `L2: Missing datum`
- `L3: Wrong validation interval`
- `L4: Missing signature`
- `L5: Spent value not OK`
- `L6: Produced value not OK`
- `L7: Public key output not spent`
- `L8: Script output not spent`
- `L9: Value minted not OK`
- `La: MustPayToPubKey`
- `Lb: MustPayToOtherScript`
- `Lc: MustHashDatum`
- `Ld: checkScriptContext failed`
- `Le: Can't find any continuing outputs`
- `Lf: Can't get any continuing outputs`
- `Lg: Can't get validator and datum hashes`
- `Lh: Can't get currency symbol of the current validator script`
- `Li: DecodingError`

### Prelude errors
- `PT1: TH Generation of Indexed Data Error`
- `PT2: PlutusTx.IsData.Class.unsafeFromBuiltinData: Void is not supported`
- `PT3: PlutusTx.Ratio: zero denominator`
- `PT5: PlutusTx.Prelude.check: input is 'False'`
- `PT6: PlutusTx.List.!!: negative index`
- `PT7: PlutusTx.List.!!: index too large`
- `PT8: PlutusTx.List.head: empty list`
- `PT9: PlutusTx.List.tail: empty list`
- `PT10: PlutusTx.Enum.().succ: bad argument`
- `PT11: PlutusTx.Enum.().pred: bad argument`
- `PT12: PlutusTx.Enum.().toEnum: bad argument`
- `PT13: PlutusTx.Enum.Bool.succ: bad argument`
- `PT14: PlutusTx.Enum.Bool.pred: bad argument`
- `PT15: PlutusTx.Enum.Bool.toEnum: bad argument`
- `PT16: PlutusTx.Enum.Ordering.succ: bad argument`
- `PT17: PlutusTx.Enum.Ordering.pred: bad argument`
- `PT18: PlutusTx.Enum.Ordering.toEnum: bad argument`
- `PT19: PlutusTx.List.last: empty list`
- `PT20: PlutusTx.Ratio.recip: reciprocal of zero`

### State machine errors
- `S0: Can't find validation input`
- `S1: State transition invalid - checks failed`
- `S2: Thread token not found`
- `S3: Non-zero value allocated in final state`
- `S4: State transition invalid - constraints not satisfied by ScriptContext`
- `S5: State transition invalid - constraints not satisfied by ScriptContext`
- `S6: State transition invalid - input is not a valid transition at the current state`
- `S7: Value minted different from expected`
- `S8: Pending transaction does not spend the designated transaction output`

### Currency errors
- `C0: Value minted different from expected`
- `C1: Pending transaction does not spend the designated transaction output`
