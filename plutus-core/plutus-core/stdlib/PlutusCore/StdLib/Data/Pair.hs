{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Built-in @pair@ and related functions.
module PlutusCore.StdLib.Data.Pair
  ( pair
  , fstPair
  , sndPair
  , uncurry
  ) where

import Prelude hiding (fst, snd, uncurry)

import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

-- | @(,)@ as a built-in PLC type.
pair :: uni `HasTypeLevel` (,) => Type tyname uni ()
pair = mkTyBuiltin @_ @(,) ()

{-| @fst@ as a PLC term.

> /\(a :: *) (b :: *) -> \(p : pair a b) -> fst {a} {b} p -}
fstPair :: TermLike term tyname name DefaultUni DefaultFun => term ()
fstPair = builtin () FstPair

{-| @snd@ as a PLC term.

> /\(a :: *) (b :: *) -> \(p : pair a b) -> snd {a} {b} p -}
sndPair :: TermLike term tyname name DefaultUni DefaultFun => term ()
sndPair = builtin () SndPair

{-| @uncurry@ as a PLC term.

> /\(a :: *) (b :: *) (c :: *) -> \(f : a -> b -> c) (p : pair a b) ->
>     f (fst {a} {b} p) (snd {a} {b} p) -}
uncurry :: TermLike term TyName Name DefaultUni DefaultFun => term ()
uncurry = runQuote $ do
  a <- freshTyName "a"
  b <- freshTyName "b"
  c <- freshTyName "c"
  f <- freshName "f"
  p <- freshName "p"
  return
    . tyAbs () a (Type ())
    . tyAbs () b (Type ())
    . tyAbs () c (Type ())
    . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () b) $ TyVar () c)
    . lamAbs () p (mkIterTyAppNoAnn pair [TyVar () a, TyVar () b])
    $ mkIterAppNoAnn
      (var () f)
      [ apply () (mkIterInstNoAnn fstPair [TyVar () a, TyVar () b]) $ var () p
      , apply () (mkIterInstNoAnn sndPair [TyVar () a, TyVar () b]) $ var () p
      ]
