{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Test.DeBruijn.Good
  ( lamAbs0
  , idFun0
  , const0
  , deepFun0
  , deeperFun0
  ) where

import PlutusPrelude
import UntypedPlutusCore

-- | A helper to intro the only "sensical" lam: debruijn binders are always 0-indexed
lamAbs0 :: t ~ Term DeBruijn uni fun () => t -> t
lamAbs0 = LamAbs () $ DeBruijn deBruijnInitIndex

-- | This is a replica of `PlutusCore.StdLib.Data.Function.idFun0` but using `DeBruijn` indices.
idFun0 :: Term DeBruijn uni fun ()
idFun0 = lamAbs0 $ Var () $ DeBruijn 1

-- | This is a replica of `PlutusCore.StdLib.Data.Function.const` but using `DeBruijn` indices.
const0 :: Term DeBruijn uni fun ()
const0 = lamAbs0 $ lamAbs0 $ Var () $ DeBruijn 2

{-| (lam0 ...n.... (Var n))
Correct binders, well-scoped variable -}
deepFun0 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deepFun0 n = timesA n lamAbs0 $ Var () $ DeBruijn $ fromIntegral n

{-|  (lam0 ...n.... lam0 ...n.... (Var n+n))
Correct binders, well-scoped variable -}
deeperFun0 :: Natural -> Term DeBruijn DefaultUni DefaultFun ()
deeperFun0 n =
  timesA n lamAbs0 $
    timesA n lamAbs0 $
      Var () $
        DeBruijn $
          fromIntegral $
            n + n
