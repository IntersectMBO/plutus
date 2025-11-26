{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module PlutusIR.Transform.RewriteRules
  ( rewriteWith
  , rewritePass
  , rewritePassSC
  , RewriteRules
  , unRewriteRules
  , defaultUniRewriteRules
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Core (HasUniques)
import PlutusCore.Name.Unique
import PlutusCore.Quote
import PlutusIR as PIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Transform.RewriteRules.Internal

import Control.Lens
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

rewritePassSC
  :: forall m uni fun a
   . ( PLC.Typecheckable uni fun
     , PLC.GEq uni
     , Ord a
     , PLC.MonadQuote m
     , Monoid a
     )
  => TC.PirTCConfig uni fun
  -> RewriteRules uni fun
  -> Pass m TyName Name uni fun a
rewritePassSC tcconfig rules =
  renamePass <> rewritePass tcconfig rules

rewritePass
  :: forall m uni fun a
   . ( PLC.Typecheckable uni fun
     , PLC.GEq uni
     , Ord a
     , PLC.MonadQuote m
     , Monoid a
     )
  => TC.PirTCConfig uni fun
  -> RewriteRules uni fun
  -> Pass m TyName Name uni fun a
rewritePass tcconfig rules =
  NamedPass "rewrite rules" $
    Pass
      (rewriteWith rules)
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig)]

{-| Rewrite a `Term` using the given `RewriteRules` (similar to functions of Term -> Term)
Normally the rewrite rules are configured at entrypoint time of the compiler.

It goes without saying that the supplied rewrite rules must be type-preserving.
MAYBE: enforce this with a `through typeCheckTerm`? -}
rewriteWith
  :: ( Monoid a
     , t ~ Term tyname Name uni fun a
     , HasUniques t
     , MonadQuote m
     )
  => RewriteRules uni fun
  -> t
  -> m t
rewriteWith rules t =
  -- We collect `VarsInfo` on the whole program term and pass it on as arg to each RewriteRule.
  -- This has the limitation that any variables newly-introduced by the rules would
  -- not be accounted in `VarsInfo`. This is currently fine, because we only rely on VarsInfo
  -- for isPure; isPure is safe w.r.t "open" terms.
  let vinfo = termVarInfo t
   in transformMOf termSubterms (unRewriteRules rules vinfo) t
