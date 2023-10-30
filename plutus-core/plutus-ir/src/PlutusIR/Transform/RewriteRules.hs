{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}
module PlutusIR.Transform.RewriteRules
    ( rewriteWith
    , RewriteRules (..)
    , defaultUniRewriteRules
    ) where

import PlutusCore.Core (HasUniques)
import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Quote
import PlutusIR as PIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Transform.RewriteRules.CommuteFnWithConst
import PlutusPrelude

import Control.Lens


-- | Rewrite a `Term` using the given `RewriteRules` (similar to functions of Term -> Term)
-- Normally the rewrite rules are configured at entrypoint time of the compiler.
rewriteWith :: ( Semigroup a, t ~ Term tyname name uni fun a
              , HasUniques t
              , MonadQuote m
              )
            => RewriteRules uni fun
            -> t
            -> m t
rewriteWith (RewriteRules rules) t =
    -- We collect `VarsInfo` on the whole program term and pass it on as arg to each RewriteRule.
    -- This has the limitation that any variables newly-introduced by the rules would
    -- not be accounted in `VarsInfo`. This is currently fine, because we only rely on VarsInfo
    -- for isPure; isPure is safe w.r.t "open" terms.
    let vinfo = termVarInfo t
    in transformMOf termSubterms (rules vinfo) t

-- | A bundle of composed `RewriteRules`, to be passed at entrypoint of the compiler.
newtype RewriteRules uni fun = RewriteRules {
    unRewriteRules :: forall tyname name m a
                   . (MonadQuote m, Semigroup a)
                   => VarsInfo tyname name uni a
                   -> PIR.Term tyname name uni fun a
                   -> m (PIR.Term tyname name uni fun a)
    }

-- | The rules for the Default Universe/Builtin.
defaultUniRewriteRules :: RewriteRules DefaultUni DefaultFun
defaultUniRewriteRules = RewriteRules $ \ _vinfo ->
        -- The rules are composed from left to right.
        pure . commuteFnWithConst
        -- e.g. >=> a follow-up rewrite rule

instance Default (RewriteRules DefaultUni DefaultFun) where
  def = defaultUniRewriteRules
