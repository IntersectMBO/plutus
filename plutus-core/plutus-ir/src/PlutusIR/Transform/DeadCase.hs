{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{-| Drops redundant `unsafeCaseList` calls produced by AsData.

See Note [Dropping redundant unsafeCaseList calls produced by AsData]. -}
module PlutusIR.Transform.DeadCase
  ( deadCase
  , deadCasePass
  , deadCasePassSC
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Name.Unique
import PlutusIR
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.Pass
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck qualified as TC

import Control.Lens (transformOf)

deadCasePassSC
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, PLC.MonadQuote m, Ord a, AnnCase a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
deadCasePassSC tcconfig =
  renamePass <> deadCasePass tcconfig

deadCasePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m, AnnCase a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
deadCasePass tcconfig =
  NamedPass "eliminate dead cases" $
    Pass
      (pure . deadCase)
      [Typechecks tcconfig]
      [ConstCondition (Typechecks tcconfig)]

{-| Eliminate @Case@ expressions marked safe-to-eliminate whose branch
binders are all dead. Uses a bottom-up traversal so that inner
eliminations cascade outward in a single pass. -}
deadCase
  :: (HasUnique name TermUnique, AnnCase a)
  => Term TyName name uni fun a
  -> Term TyName name uni fun a
deadCase = transformOf termSubterms processTerm

processTerm
  :: (HasUnique name TermUnique, AnnCase a)
  => Term TyName name uni fun a
  -> Term TyName name uni fun a
processTerm = \case
  Case a _resTy _scrut [LamAbs _ x _ (LamAbs _ y _ body)]
    | annIsSafeToDrop a
    , let usages = Usages.termUsages body
    , Usages.getUsageCount x usages == 0
    , Usages.getUsageCount y usages == 0 ->
        body
  other -> other
