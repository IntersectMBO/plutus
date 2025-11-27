{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module PlutusIR.Transform.RewriteRules.Internal
  ( RewriteRules (..)
  , defaultUniRewriteRules
  ) where

import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Name.Unique (Name)
import PlutusCore.Quote (MonadQuote)
import PlutusIR.Analysis.VarInfo (VarsInfo)
import PlutusIR.Core.Type qualified as PIR
import PlutusIR.Transform.RewriteRules.CommuteFnWithConst (commuteFnWithConst)
import PlutusIR.Transform.RewriteRules.UnConstrConstrData (unConstrConstrData)
import PlutusPrelude (Default (..), (>=>))

-- | A bundle of composed `RewriteRules`, to be passed at entrypoint of the compiler.
newtype RewriteRules uni fun where
  RewriteRules
    :: { unRewriteRules
           :: forall tyname m a
            . (MonadQuote m, Monoid a)
           => VarsInfo tyname Name uni a
           -> PIR.Term tyname Name uni fun a
           -> m (PIR.Term tyname Name uni fun a)
       }
    -> RewriteRules uni fun

-- | The rules for the Default Universe/Builtin.
defaultUniRewriteRules :: RewriteRules DefaultUni DefaultFun
defaultUniRewriteRules = RewriteRules $ \varsInfo ->
  -- The rules are composed from left to right.
  pure . commuteFnWithConst >=> unConstrConstrData def varsInfo

instance Default (RewriteRules DefaultUni DefaultFun) where
  def = defaultUniRewriteRules

instance Semigroup (RewriteRules uni fun) where
  RewriteRules r1 <> RewriteRules r2 = RewriteRules (\varsInfo -> r1 varsInfo >=> r2 varsInfo)

instance Monoid (RewriteRules uni fun) where
  mempty = RewriteRules (const pure)
