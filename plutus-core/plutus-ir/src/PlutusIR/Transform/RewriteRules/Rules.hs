{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
module PlutusIR.Transform.RewriteRules.Rules where

import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusCore.Quote
import PlutusIR as PIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Transform.RewriteRules.CommuteFnWithConst
import PlutusIR.Transform.RewriteRules.UnConstrConstrData
import PlutusPrelude

-- | A bundle of composed `RewriteRules`, to be passed at entrypoint of the compiler.
newtype RewriteRules uni fun where
  RewriteRules :: {unRewriteRules :: forall tyname m a.
                                       (MonadQuote m, Monoid a) =>
                                       VarsInfo tyname Name uni a
                                       -> PIR.Term tyname Name uni fun a
                                          -> m (PIR.Term tyname Name uni fun a)}
                    -> RewriteRules uni fun

-- | The rules for the Default Universe/Builtin.
defaultUniRewriteRules :: RewriteRules DefaultUni DefaultFun
defaultUniRewriteRules = RewriteRules $ \ vinfo ->
        -- The rules are composed from left to right.
        pure . commuteFnWithConst
        >=> unConstrConstrData def vinfo

instance Default (RewriteRules DefaultUni DefaultFun) where
  def = defaultUniRewriteRules
