-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UntypedPlutusCore.Check.Scope (checkScope) where

import Control.Lens hiding (index)
import UntypedPlutusCore.Core.Type as UPLC
import UntypedPlutusCore.DeBruijn as UPLC

import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)

{-| A pass to check that the input term:
1) does not contain free variables and
2) that all binders are set to debruijn index 0.

Feeding the result of the debruijnification to this function is expected to pass.

On the other hand, because of (2), this pass is
stricter than the undebruijnification's (indirect)
scope-checking, see Note [DeBruijn indices of Binders].

Inlining this function makes a big difference,
since it will usually be called in a context where all the type variables are known.
That then means that GHC can optimize go locally in a completely monomorphic setting, which helps a lot. -}
checkScope
  :: forall m name uni fun a
   . (HasIndex name, MonadError FreeVariableError m)
  => UPLC.Term name uni fun a
  -> m ()
checkScope = go 0
  where
    -- the current level as a reader value
    go :: Word -> UPLC.Term name uni fun a -> m ()
    go !lvl = \case
      Var _ n -> do
        let i = n ^. index
        -- var index must be larger than 0
        -- var index must be LEQ to the current level
        unless (i > 0 && fromIntegral i <= lvl) $
          throwError $
            FreeIndex i
      LamAbs _ binder t -> do
        let bIx = binder ^. index
        -- binder index must be equal to 0
        unless (bIx == 0) $
          throwError $
            FreeIndex bIx
        go (lvl + 1) t
      Apply _ t1 t2 -> go lvl t1 >> go lvl t2
      Force _ t -> go lvl t
      Delay _ t -> go lvl t
      _ -> pure ()
{-# INLINE checkScope #-}
