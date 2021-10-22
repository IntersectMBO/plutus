{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}
-- | Optimization passes for removing dead code, mainly dead let bindings.
module PlutusIR.Transform.DeadCode (removeDeadBindings) where

import           PlutusIR
import qualified PlutusIR.Analysis.Dependencies as Deps
import           PlutusIR.MkPir
import           PlutusIR.Transform.Rename      ()

import qualified PlutusCore                     as PLC
import qualified PlutusCore.Constant            as PLC
import qualified PlutusCore.Name                as PLC

import           Control.Lens
import           Control.Monad.Extra            (mapMaybeM)
import           Control.Monad.Reader

import           Data.Coerce
import qualified Data.Set                       as Set

import qualified Algebra.Graph                  as G
import qualified Algebra.Graph.ToGraph          as T
import qualified Data.List.NonEmpty             as NE

type TruncateTypes = Bool

-- | Remove all the dead let bindings in a term.
removeDeadBindings ::
    ( PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    , PLC.MonadQuote m
    )
    => TruncateTypes
    -> Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
removeDeadBindings tt t = do
    tRen <- PLC.rename t
    runReaderT (transformMOf termSubterms processTerm tRen)
               (Ctx (calculateLiveness tRen) tt)

type Liveness = Set.Set Deps.Node
data Ctx = Ctx Liveness TruncateTypes

calculateLiveness ::
    ( PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    , PLC.ToBuiltinMeaning uni fun
    )
    => Term tyname name uni fun a
    -> Liveness
calculateLiveness t =
    let depGraph :: G.Graph Deps.Node
        depGraph = fst $ Deps.runTermDeps t
    in Set.fromList $ T.reachable Deps.Root depGraph

live :: (MonadReader Ctx m, PLC.HasUnique n unique) => n -> m Bool
live n = do
    Ctx liveness _ <- ask
    let u = coerce $ n ^. PLC.unique
    pure $ Set.member (Deps.Variable u) liveness

-- TODO: Refactor drunk code
liveBinding ::
    ( MonadReader Ctx m
    , PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    )
    => Binding tyname name uni fun a
    -> m (Maybe (Binding tyname name uni fun a))
liveBinding b = do
    Ctx _ truncateTypes <- ask
    let -- TODO: HasUnique instances for VarDecl and TyVarDecl?
        liveVarDecl (VarDecl _ n _) = live n
        liveTyVarDecl (TyVarDecl _ n _) = live n
        f True = Just b
        f _    = Nothing
    case b of
        TermBind _ _ d _ -> f <$> liveVarDecl d
        TypeBind _ d _ -> f <$> liveTyVarDecl d
        DatatypeBind a (Datatype a' d t destr constrs) ->
            if truncateTypes -- Allow the removal of unused constructors
            then liveTyVarDecl d >>= \case
                True -> filterM liveVarDecl constrs >>= \constrs' ->
                    -- #4147: An empty `constrs'` here basically means a type that is only used at the type level.
                    -- Not sure if inlining it would make the script smaller, will test around a bit more.
                    -- Also, will a type binding work?
                    pure $ Just (DatatypeBind a (Datatype a' d t destr constrs'))
                _ -> pure Nothing
            else pure (Just b)

processTerm ::
    ( MonadReader Ctx m
    , PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    )
    => Term tyname name uni fun a
    -> m (Term tyname name uni fun a)
processTerm = \case
    -- throw away dead bindings
    Let x r bs t -> mkLet x r <$> mapMaybeM liveBinding (NE.toList bs) <*> pure t
    x            -> pure x
