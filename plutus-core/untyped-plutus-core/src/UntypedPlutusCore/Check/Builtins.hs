{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Check.Builtins (checkBuiltins) where

import PlutusCore (SomeTypeIn, someValueType)
import UntypedPlutusCore.Core

-- Want this to inline so that 'go' can be specialized to the predicate.
-- Probably it will be, but just make sure GHC can see it.
{-# INLINABLE checkBuiltins #-}
-- | Run a predicate over the builtin functions and builtin types used in the term.
checkBuiltins
    :: Monad m
    => (fun -> m ())
    -> (SomeTypeIn uni -> m ())
    -> Term name uni fun a
    -> m ()
checkBuiltins pfun puni = go
  where
      go = \case
        LamAbs _ _ t  -> go t
        Apply _ t1 t2 -> go t1 >> go t2
        Force _ t     -> go t
        Delay _ t     -> go t
        Builtin _ f   -> pfun f
        Constant _ c  -> puni (someValueType c)
        _             -> pure ()
