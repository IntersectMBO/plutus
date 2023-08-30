-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module PlutusIR.Transform.DeadCode (removeDeadBindings) where

import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.MkPir
import PlutusIR.Transform.Rename ()

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name qualified as PLC

import Control.Lens
import Control.Monad.Reader

import Data.Coerce
import Data.Set qualified as Set

import Algebra.Graph qualified as G
import Algebra.Graph.ToGraph qualified as T
import Data.List.NonEmpty qualified as NE
import PlutusCore.Quote (MonadQuote, freshTyName, liftQuote)
import PlutusCore.StdLib.Data.ScottUnit qualified as Unit
import Witherable (Witherable (wither))

-- | Remove all the dead let bindings in a term.
removeDeadBindings
    :: (PLC.HasUnique name PLC.TermUnique,
       PLC.ToBuiltinMeaning uni fun, PLC.MonadQuote m)
    => PLC.BuiltinSemanticsVariant fun
    -> Term TyName name uni fun a
    -> m (Term TyName name uni fun a)
removeDeadBindings semvar t = do
    tRen <- PLC.rename t
    liftQuote $ runReaderT (transformMOf termSubterms processTerm tRen) (calculateLiveness semvar tRen)

type Liveness = Set.Set Deps.Node

calculateLiveness
    :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique,
       PLC.ToBuiltinMeaning uni fun)
    => PLC.BuiltinSemanticsVariant fun
    -> Term tyname name uni fun a
    -> Liveness
calculateLiveness semvar t =
    let
        depGraph :: G.Graph Deps.Node
        depGraph = fst $ Deps.runTermDeps semvar t
    in Set.fromList $ T.reachable depGraph Deps.Root

live :: (MonadReader Liveness m, PLC.HasUnique n unique) => n -> m Bool
live n =
    let
        u = coerce $ n ^. PLC.unique
    in asks $ Set.member (Deps.Variable u)

liveBinding
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, MonadQuote m)
    => Binding TyName name uni fun a
    -> m (Maybe (Binding TyName name uni fun a))
liveBinding =
    let
        -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        liveVarDecl (VarDecl _ n _) = live n
        liveTyVarDecl (TyVarDecl _ n _) = live n
    in \case
        b@(TermBind _ _ d _) -> do
            l <- liveVarDecl d
            pure $ if l then Just b else Nothing
        b@(TypeBind _ d _) -> do
            l <- liveTyVarDecl d
            pure $ if l then Just b else Nothing
        b@(DatatypeBind x (Datatype _ d _ destr constrs)) -> do
            dtypeLive <- liveTyVarDecl d
            destrLive <- live destr
            constrsLive <- traverse liveVarDecl constrs
            let termLive = or (destrLive : constrsLive)
            case (dtypeLive, termLive) of
                 -- At least one term-level part is live, keep the whole thing
                (_, True)      -> pure $ Just b
                -- Nothing is live, remove the whole thing
                (False, False) -> pure Nothing
                -- See Note [Dependencies for datatype bindings, and pruning them]
                 -- Datatype is live but no term-level parts are, replace with a trivial type binding
                (True, False)  -> Just . TypeBind x d <$> mkTypeOfKind (_tyVarDeclKind d)

-- | Given a kind, make a type (any type!) of that kind.
-- Generates things of the form 'unit -> unit -> ... -> unit'
mkTypeOfKind :: MonadQuote m => Kind a -> m (Type TyName uni a)
mkTypeOfKind = \case
    -- The scott-encoded unit here is a little bulky but it continues to be the easiest
    -- way to get a type of kind Type without relying on builtins.
    Type a -> pure $ a <$ Unit.unit
    KindArrow a ki ki' -> do
        n <- freshTyName "a"
        TyLam a n ki <$> mkTypeOfKind ki'

processTerm
    :: (MonadReader Liveness m, PLC.HasUnique name PLC.TermUnique, MonadQuote m)
    => Term TyName name uni fun a
    -> m (Term TyName name uni fun a)
processTerm = \case
    -- throw away dead bindings
    Let x r bs t -> mkLet x r <$> wither liveBinding (NE.toList bs) <*> pure t
    x            -> pure x
