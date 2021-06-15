-- | Built-in @pair@ and related functions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.Pair
    ( pair
    , fst
    , snd
    , uncurry
    ) where

import           Prelude            hiding (fst, snd, uncurry)

import           PlutusCore.Core
import           PlutusCore.Default
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote

-- | @(,)@ as a built-in PLC type.
pair :: uni `Contains` (,) => Type TyName uni ()
pair = mkTyBuiltin @_ @(,) ()

-- | @fst@ as a PLC term.
--
-- > /\(a :: *) (b :: *) -> \(p : pair a b) -> fst {a} {b} p
fst :: TermLike term TyName Name DefaultUni DefaultFun => term ()
fst = builtin () Fst

-- | @snd@ as a PLC term.
--
-- > /\(a :: *) (b :: *) -> \(p : pair a b) -> snd {a} {b} p
snd :: TermLike term TyName Name DefaultUni DefaultFun => term ()
snd = builtin () Snd

-- | @uncurry@ as a PLC term.
--
-- > /\(a :: *) (b :: *) (c :: *) -> \(f : a -> b -> c) (p : pair a b) ->
-- >     f (fst {a} {b} p) (snd {a} {b} p)
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
        . lamAbs () p (mkIterTyApp () pair [TyVar () a, TyVar () b])
        $ mkIterApp () (var () f)
            [ apply () (mkIterInst () fst [TyVar () a, TyVar () b]) $ var () p
            , apply () (mkIterInst () snd [TyVar () a, TyVar () b]) $ var () p
            ]
