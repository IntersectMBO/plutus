{-# LANGUAGE LambdaCase #-}

module PlutusIR.Transform.LetFloatFromScrutinee (floatTerm, floatTermPass, floatTermPassSC) where

import PlutusCore qualified as PLC
import PlutusCore.Name.Unique qualified as PLC
import PlutusIR
import PlutusIR.Analysis.VarInfo
import PlutusIR.Contexts
import PlutusIR.MkPir
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

import Control.Lens hiding (Strict)
import Data.List.NonEmpty.Extra (NonEmpty (..))
import Data.List.NonEmpty.Extra qualified as NonEmpty
import Data.Tuple.Extra

data Let tyname name uni fun a = MkLet a Recursivity (NonEmpty (Binding tyname name uni fun a))

floatTermPassSC
  :: forall m uni fun a
   . ( PLC.Typecheckable uni fun
     , PLC.GEq uni
     , Ord a
     , PLC.MonadQuote m
     )
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
floatTermPassSC tcconfig =
  renamePass <> floatTermPass tcconfig

floatTermPass
  :: forall m uni fun a
   . ( PLC.Typecheckable uni fun
     , PLC.GEq uni
     , Ord a
     , Applicative m
     )
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
floatTermPass tcconfig =
  NamedPass "let float from scrutinee" $
    Pass
      (pure . floatTerm)
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig)]

-- | Float bindings in the given `Term` inwards.
floatTerm
  :: forall tyname name uni fun a
   . ( PLC.HasUnique name PLC.TermUnique
     , PLC.HasUnique tyname PLC.TypeUnique
     )
  => Term tyname name uni fun a
  -> Term tyname name uni fun a
floatTerm t =
  let vinfo = termVarInfo t
   in transformOf termSubterms (processTerm vinfo) t

processTerm
  :: forall tyname name uni fun a
   . ( PLC.HasUnique name PLC.TermUnique
     , PLC.HasUnique tyname PLC.TypeUnique
     )
  => VarsInfo tyname name uni a
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
processTerm vinfo t
  | (v@(Var _ n), args) <- splitApplication t
  , Just (DatatypeMatcher parentName) <- lookupVarInfo n vinfo
  , Just (DatatypeTyVar (Datatype _ _ tvs _ _)) <- lookupTyVarInfo parentName vinfo
  , (ctx0, TermAppContext scrut a ctx1) <-
      -- The first @length tvs@ layers are for the datatype's type arguments.
      splitAppContext (length tvs) args =
      let (lets, scrut') = collectBindings scrut
       in mkLets lets . fillAppContext v . appendAppContext ctx0 $
            TermAppContext scrut' a ctx1
  | otherwise = t

-- | Strip off let-bindings. Bindings in the outer-most @Let@ appear first in the result.
collectBindings
  :: Term tyname name uni fun a
  -> ([Let tyname name uni fun a], Term tyname name uni fun a)
collectBindings = \case
  Let a r bs body -> first (MkLet a r bs :) (collectBindings body)
  other -> ([], other)

{-| Wrap the @Let@s around the term. The first @Let@ appears as the
outer-most @Let@ in the result.
-}
mkLets :: [Let tyname name uni fun a] -> Term tyname name uni fun a -> Term tyname name uni fun a
mkLets = flip . foldr $ \(MkLet a r bs) -> mkLet a r (NonEmpty.toList bs)
