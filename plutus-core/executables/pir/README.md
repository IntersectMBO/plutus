A small tool to help with rapid interation when working with Plutus IR compiler.

For instance, when debugging an issue when compiling a file from the `marlowe`
package, we can:

- dump the PIR of the troublesome Plutus IR term,
- modify the compiler, and
- re-run the compiler on the dumped PIR term, without the need to rebuild
  `marlowe` and all of its dependencies.

# Dumping PIR

Plutus plugin supports dumping binary representation of the PIR via `dump-pir-flat`:

```haskell
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-pir-flat #-}
```

The PIR binary dump file dumps to `plutus/plutus-core/` and has the name as the module name followed by a brief description and ".flat".
# Debugging PIR Compilation

When dealing with issues with PIR compilation, we can simply re-run the
compiler on the dumped PIR flat file:

```bash
cabal run plutus-core:pir -- FILE.flat
```

`cabal run` should take care of rebuilding the compiler, so the issue of stale
plugin does not arise.

# Profiling PIR -> PLC Compilation

We can also profile the evaluation.

```bash
cabal run plutus-core:pir --enable-profiling -- FILE.flat
```

