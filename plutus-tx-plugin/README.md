# GHC Core to Plutus Core converter and plugin

This package is a library which allows converting GHC Core into Plutus Core, with the aim of allowing people to write Plutus contracts in surface Haskell.

The package also contains a compiler plugin which looks for specially tagged expressions and applies the converter. This should not usually be used directly, 
but rather via [plutus-tx](../plutus-tx/README.md).

## Debugging

The plugin can produce somewhat intimidating errors. In particular it can be hard to work out which expression
is responsible for an error. To improve this you can compile the file in question with the `-g` GHC option. This
will result in additional source spans being put into the program which will appear in errors.

