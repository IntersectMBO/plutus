---
sidebar_position: 10
---

# Compiling Plinth

The Plinth compiler is a GHC plugin, provided by the `plutus-tx-plugin` package.
There are two ways to invoke the plugin: via Template Haskell (preferred) or using a GHC flag.

Let’s assume we want to compile the following code:

```haskell
module A where

import qualified PlutusTx.Prelude as PlutusTx

myPlutusTxCode :: Integer -> Integer
myPlutusTxCode x = x PlutusTx.+ 1
```

> :pushpin: **NOTE**
>
> There are some GHC extensions, flags and pragmas recommended for modules containing Plinth code, but these are omitted here.
> You can find more information in [GHC Extensions, Flags and Pragmas](./extensions-flags-pragmas.md).

## Compiling Using Template Haskell (Preferred)

Here's how to compile `myPlutusTxCode` using Template Haskell:

```haskell
{-# LANGUAGE TemplateHaskell #-}
module B where

import PlutusTx.Code (CompiledCode)
import PlutusTx.TH (compile)

myPlutusTxCodeCompiled :: CompiledCode (Integer -> Integer)
myPlutusTxCodeCompiled = $$(compile [|| myPlutusTxCode ||])
```

Under the hood, it uses [`addCorePlugin`](https://hackage.haskell.org/package/template-haskell/docs/Language-Haskell-TH-Syntax.html#v:addCorePlugin) from the `template-haskell` package to install the plugin into the compilation pipeline.

You can then compile module `B` as you would any regular Haskell module.
The resulting `CompiledCode` contains the UPLC code, and also includes PIR for debugging.

Template Haskell is a complicated piece of machinery, but as you can see, you need to understand almost none of it for the purpose of compiling Plinth.

This method is preferred since it can leverage Template Haskell's [`location`](https://hackage.haskell.org/package/template-haskell/docs/Language-Haskell-TH.html#v:location) function to pass the location of `$$(compile [|| ... ||])` to the plugin, which is used in error messages.

## Compiling Using GHC Flag

An alternative way to compile `myPlutusTxCode` is by using the `-fplugin` GHC flag, which installs a plugin into the pipeline.
Use this flag with the `plc` function:

```haskell
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
module B where

import Data.Proxy
import PlutusTx.Code (CompiledCode)
import PlutusTx.Plugin (plc)

myPlutusTxCodeCompiled :: CompiledCode (Integer -> Integer)
myPlutusTxCodeCompiled = plc (Proxy @"location info") myPlutusTxCode
```

Here you can manually provide the location info to be included in error messages, but it's not essential, especially if `plc` is only called once in the module, since there won't be any confusion about which `plc` is causing the issue if the module fails to compile.

The `-fplugin` flag must be used on every module that invokes `plc`.
