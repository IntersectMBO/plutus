{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

{-| A top-down pass converting 2 or more consecutive casing on lists,
if the heads are all unused, and the tails are all unused except for
being immediately matched on.

Example:

case xs of _h1 t1 ->
  case t1 of _h2 t2 ->
    case t2 of _h3 t3 ->
      case t3 of _h4 t4 ->
        case t4 of h5 t5 -> ...t5...

===>

case (drop 4 xs) of h5 t5 -> ...t5... -}
module PlutusIR.Transform.CollapseCase
  ( collapseCase
  , collapseCasePassSC
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Analysis.Usages qualified as Usages
import PlutusCore.Annotation
import PlutusCore.Name.Unique
import PlutusIR
import PlutusIR.Pass
import PlutusIR.Subst (termUsages)
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck qualified as TC

import Control.Lens (over, transformOf, view)

collapseCasePassSC
  :: (uni ~ PLC.DefaultUni, fun ~ PLC.DefaultFun, Applicative m, AnnCase a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
collapseCasePassSC tcconfig =
  NamedPass "collapse cases on lists into dropLists" $
    Pass
      (pure . collapseCase)
      [Typechecks tcconfig]
      [ConstCondition (Typechecks tcconfig)]

collapseCase
  :: forall name uni fun a
   . ( uni ~ PLC.DefaultUni
     , fun ~ PLC.DefaultFun
     , HasUnique name TermUnique
     , AnnCase a
     )
  => Term TyName name uni fun a
  -> Term TyName name uni fun a
collapseCase t = maybe (over termSubterms collapseCase t) collapseCase (collapse t)
  where
    collapse = \case
      -- First casing in the sequence - go from here
      Case a _resTy scrut [LamAbs _ hd elemTy (LamAbs _ tl _ body)]
        | annIsSafeToDrop a
        , Usages.getUsageCount hd (termUsages body) == 0 ->
            go (1 :: Integer) (getAnn scrut) scrut elemTy tl body
      _ -> Nothing

    go
      :: Integer
      -> a
      -- \^ annotation on the first scrutinee in the sequence
      -> Term TyName name uni fun a
      -- \^ first scrutinee in the sequence
      -> Type TyName uni a
      -- \^ list element type
      -> name
      -- \^ current tail
      -> Term TyName name uni fun a
      -- \^ current body
      -> Maybe (Term TyName name uni fun a)
    go k aTop scrutTop elemTy tl0 body0 = case body0 of
      Case a _resTy (Var _ scrut) [LamAbs _ hd _tyElem' (LamAbs _ tl _ body)]
        | annIsSafeToDrop a
        , view theUnique scrut == view theUnique tl0
        , let usages = termUsages body
        , -- new head must be unused in the body for the sequence to continue
          Usages.getUsageCount hd usages == 0
        , -- original tail must be unused in the body for the sequence to continue
          Usages.getUsageCount tl0 usages == 0 ->
            -- recursive with new tail and new body
            go (k + 1) aTop scrutTop elemTy tl body
      _
        | Usages.getUsageCount tl0 (termUsages body0) == 1
        , k >= 2 ->
            Just $ substVar tl0 dropped body0
        | otherwise -> Nothing
      where
        dropped = mkDrop aTop k elemTy scrutTop

        substVar n new = transformOf termSubterms $ \case
          Var _ v | view theUnique v == view theUnique n -> new
          other -> other

    mkDrop
      :: a
      -> Integer
      -> Type TyName uni a
      -> Term TyName name uni fun a
      -> Term TyName name uni fun a
    mkDrop ann k elemTy =
      Apply
        ann
        ( Apply
            ann
            (TyInst ann (Builtin ann PLC.DropList) elemTy)
            (Constant ann (PLC.someValue k))
        )
