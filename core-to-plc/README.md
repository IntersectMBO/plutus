# GHC Core to Plutus Core converter and plugin

This package is a library which allows converting GHC Core into Plutus Core, with the aim of allowing people to write Plutus contracts in surface Haskell.

The package also contains a compiler plugin which looks for specially tagged expressions and applies the converter. This should not usually be used directly, but rather via a Template Haskell frontend that handles the details.
