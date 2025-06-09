---
title: Base
layout: page
---
```
module Evaluator.Base where

```

## Imports

```
open import Agda.Builtin.Nat
open import Data.String using (String;_++_)

open import Check using (TypeError)
open TypeError
open import Scoped using (FreeVariableError;ScopeError;extricateScopeTy)
open import Scoped.Extrication using (extricateNf⋆)
open import Raw using (RawTm;RawTy)
import RawU as U using (Untyped)
open import Utils using (RuntimeError)
open RuntimeError
```

```
postulate
    ParseError : Set

{-# FOREIGN GHC import PlutusCore.Pretty #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import PlutusCore.Error #-}
{-# COMPILE GHC ParseError = type PlutusCore.Error.ParserErrorBundle #-}

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

  prettyPrintUTm : U.Untyped → String

{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# COMPILE GHC prettyPrintTm = display @T.Text . unconv 0 #-}
{-# COMPILE GHC prettyPrintTy = display @T.Text . unconvT 0 #-}

{-# FOREIGN GHC import qualified FFI.Untyped as U #-}
{-# COMPILE GHC prettyPrintUTm = display @T.Text . U.uconv 0 #-}
```

## Error

```
-- the Error's returned by `plc-agda` and the haskell interface to `metatheory`.

data ERROR : Set where
  typeError : String → ERROR
  parseError : ParseError → ERROR
  scopeError : ScopeError → ERROR
  runtimeError : RuntimeError → ERROR
  jsonError : String → ERROR
```

Ugly printing of Type Errors

```
uglyTypeError : TypeError → String
uglyTypeError (kindMismatch K K' x) = "kindMismatch"
uglyTypeError (notFunKind K x) = "NotFunKind"
uglyTypeError (notPat K x) = "notPat"
uglyTypeError UnknownType = "UnknownType"
uglyTypeError (notPi A x) = "notPi"
uglyTypeError (notMu A x) = "notMu"
uglyTypeError (notFunType A x) = "notFunType"
uglyTypeError (typeMismatch A A' x) =
  prettyPrintTy (extricateScopeTy (extricateNf⋆ A))
  ++
  " doesn't match "
  ++
  prettyPrintTy (extricateScopeTy (extricateNf⋆ A'))
uglyTypeError builtinError = "builtinError"
uglyTypeError (Unimplemented x) = "Feature " ++ x ++ " not implemented"
uglyTypeError (notSOP A x) = "notSOP" ++ prettyPrintTy (extricateScopeTy (extricateNf⋆ A))
uglyTypeError (IndexOutOfBounds x) = "IndexOutOfBounds"
uglyTypeError TooManyConstrArgs = "TooManyConstrArgs"
uglyTypeError TooFewConstrArgs = "TooFewConstrArgs"
uglyTypeError TooFewCases = "TooFewCases"
uglyTypeError TooManyCases = "TooManyCases"

-- the haskell version of Error is defined in Raw
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC ERROR = data ERROR (TypeError | ParseError | ScopeError | RuntimeError | JsonError) #-}
```

```
reportError : ERROR → String
reportError (parseError _) = "parseError"
reportError (typeError s) = "typeError: " ++ s
reportError (jsonError s) = "jsonError: " ++ s
reportError (scopeError _) = "scopeError"
reportError (runtimeError gasError)         = "gasError"
reportError (runtimeError userError)        = "userError"
reportError (runtimeError runtimeTypeError) = "runtimeTypeError"
```


## Maximum number of steps machine should make

```
maxsteps : Nat
maxsteps = 10000000000
```
