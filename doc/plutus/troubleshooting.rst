Troubleshooting
===============

Plugin errors
-------------

Errors that start with ``GHC Core to PLC plugin`` are ``plutus-tx-plugin`` errors.
The most common error is:

``Error: Reference to a name which is not a local, a builtin, or an external INLINABLE function``

This means the plugin doesn't have access to implementation of the function, which it needs to be able to compile the function to Plutus Core.
Some things you can do to fix it:

- Make sure to add ``{-# INLINABLE functionname #-}`` to your function.
- If there's an extra ``$c`` in front of the function name in the error, GHC has generated a specialised version of your function,
  which prevents the plugin from accessing it.
  You can turn it off with ``{-# OPTIONS_GHC -fno-specialise #-}``
- Other compiler options that could fix the issue are

  - ``{-# OPTIONS_GHC -fno-strictness #-}``
  - ``{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}``
  - ``{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}``
  - ``{-# OPTIONS_GHC -fobject-code #-}``

  Some more details are in `the plutus-tx readme <https://github.com/input-output-hk/plutus/tree/master/plutus-tx#building-projects-with-plutus-tx>`_.

If you don't need the plugin to succeed, f.e. when Haddock is building documentation,
you can pass the GHC option ``-fplugin-opt Plutus.Tx.Plugin:defer-errors`` as a cli parameter::

  cabal repl --ghc-options -fplugin-opt PlutusTx.Plugin:defer-errors plutus-contract

or add the following lines for your ``package-name`` to ``cabal.project``::

  package your-package
    haddock-options: "--optghc=-fplugin-opt PlutusTx.Plugin:defer-errors"


.. note::
  The recommended way to build documentation is with ``nix-build default.nix -A docs.site``


Haskell language server issues
------------------------------

``ghcide compiled against GHC 8.10.3 but currently using 8.10.2.20201118``

Your editor is not picking up the right version of the haskell language server (HLS).
Plutus needs a custom version of HLS which is provided by Nix. So get this working in your editor, make sure to do these two things:

- Start your editor from ``nix-shell``.
- Most editors are configured to use ``haskell-language-server-wrapper``, which is a wrapper which picks the right HSL version.
  Change this to just ``haskell-language-server``.

If this doesn't work, run ``which haskell-language-server`` in `nix-shell`, and use this absolute path in the configuration of your editor.


Error codes
-----------

To reduce code size, on-chain errors only output codes. Here's what they mean:

..
  This list can be generated with:
  grep -rEoh "\btrace\w*\s+\"[^\"]{1,5}\"\s+(--.*|\{-\".*\"-\})" *

- Ledger errors

  - ``L0: Input constraint``
  - ``L1: Output constraint``
  - ``L2: Missing datum``
  - ``L3: Wrong validation interval``
  - ``L4: Missing signature``
  - ``L5: Spent value not OK``
  - ``L6: Produced value not OK``
  - ``L7: Public key output not spent``
  - ``L8: Script output not spent``
  - ``L9: Value minted not OK``
  - ``La: MustPayToPubKey``
  - ``Lb: MustPayToOtherScript``
  - ``Lc: MustHashDatum``
  - ``Ld: checkScriptContext failed``
  - ``Le: Can't find any continuing outputs``
  - ``Lf: Can't get any continuing outputs``
  - ``Lg: Can't get validator and datum hashes``
  - ``Lh: Can't get currency symbol of the current validator script``
  - ``Li: DecodingError``

- Prelude errors

  - ``P0: PlutusTx.Enum.().succ: bad argument``
  - ``P1: PlutusTx.Enum.().pred: bad argument``
  - ``P2: PlutusTx.Enum.().toEnum: bad argument``
  - ``P3: PlutusTx.Enum.Bool.succ: bad argument``
  - ``P4: PlutusTx.Enum.Bool.pred: bad argument``
  - ``P5: PlutusTx.Enum.Bool.toEnum: bad argument``
  - ``P6: PlutusTx.Enum.Ordering.succ: bad argument``
  - ``P7: PlutusTx.Enum.Ordering.pred: bad argument``
  - ``P8: PlutusTx.Enum.Ordering.toEnum: bad argument``
  - ``P9: PlutusTx.List.!!: negative index``
  - ``Pa: PlutusTx.List.!!: index too large``
  - ``Pb: PlutusTx.List.head: empty list``
  - ``Pc: PlutusTx.List.tail: empty list``
  - ``Pd: Check has failed``
  - ``Pe: Ratio has zero denominator``
  - ``Pf: round default defn: Bad value``
  - ``Pg: unsafeFromBuiltinData: Void is not supported``

- State machine errors

  - ``S0: Can't find validation input``
  - ``S1: State transition invalid - checks failed``
  - ``S2: Thread token not found``
  - ``S3: Non-zero value allocated in final state``
  - ``S4: State transition invalid - constraints not satisfied by ScriptContext``
  - ``S5: State transition invalid - constraints not satisfied by ScriptContext``
  - ``S6: State transition invalid - input is not a valid transition at the current state``
  - ``S7: Value minted different from expected``
  - ``S8: Pending transaction does not spend the designated transaction output``

- Currency errors

  - ``C0: Value minted different from expected``
  - ``C1: Pending transaction does not spend the designated transaction output``
