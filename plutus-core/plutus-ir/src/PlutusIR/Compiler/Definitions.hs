{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | Support for generating PIR with global definitions with dependencies between them.
module PlutusIR.Compiler.Definitions (DefT
                                              , MonadDefs (..)
                                              , TermDefWithStrictness
                                              , runDefT
                                              , defineTerm
                                              , defineType
                                              , defineDatatype
                                              , recordAlias
                                              , lookupTerm
                                              , lookupOrDefineTerm
                                              , lookupType
                                              , lookupOrDefineType
                                              , lookupConstructors
                                              , lookupDestructor) where

import           PlutusIR
import           PlutusIR.MkPir                       hiding (error)

import qualified PlutusCore.MkPlc                     as PLC
import           PlutusCore.Quote

import           Control.Lens
import           Control.Monad.Except
import qualified Control.Monad.Morph                  as MM
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Algebra.Graph.AdjacencyMap           as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap  as NAM
import qualified Algebra.Graph.ToGraph                as Graph

import           Data.Foldable
import qualified Data.Map                             as Map
import           Data.Maybe
import qualified Data.Set                             as Set

-- | A map from keys to pairs of bindings and their dependencies (as a list of keys).
type DefMap key def = Map.Map key (def, Set.Set key)

mapDefs :: (a -> b) -> DefMap key a -> DefMap key b
mapDefs f = Map.map (\(def, deps) -> (f def, deps))

type TermDefWithStrictness uni fun ann =
    PLC.Def (VarDecl TyName Name uni fun ann) (Term TyName Name uni fun ann, Strictness)

data DefState key uni fun ann = DefState {
    _termDefs     :: DefMap key (TermDefWithStrictness uni fun ann),
    _typeDefs     :: DefMap key (TypeDef TyName uni ann),
    _datatypeDefs :: DefMap key (DatatypeDef TyName Name uni fun ann),
    _aliases      :: Set.Set key
    }
makeLenses ''DefState

newtype DefT key uni fun ann m a = DefT { unDefT :: StateT (DefState key uni fun ann) m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadError e, MonadReader r, MonadQuote)

-- Need to write this by hand, deriving wants to derive the one for DefState
instance MonadState s m => MonadState s (DefT key uni fun ann m) where
    get = lift get
    put = lift . put
    state = lift . state

-- TODO: provenances
runDefT :: (Monad m, Ord key) => ann -> DefT key uni fun ann m (Term TyName Name uni fun ann) -> m (Term TyName Name uni fun ann)
runDefT x act = do
    (term, s) <- runStateT (unDefT act) (DefState mempty mempty mempty mempty)
    pure $ wrapWithDefs x (bindingDefs s) term
        where
            bindingDefs defs =
                let
                    terms = mapDefs (\d -> TermBind x (snd $ PLC.defVal d) (PLC.defVar d) (fst $ PLC.defVal d)) (_termDefs defs)
                    types = mapDefs (\d -> TypeBind x (PLC.defVar d) (PLC.defVal d)) (_typeDefs defs)
                    datatypes = mapDefs (\d -> DatatypeBind x (PLC.defVal d)) (_datatypeDefs defs)
                in terms `Map.union` types `Map.union` datatypes

-- | Given the definitions in the program, create a topologically ordered list of the
-- SCCs using the dependency information
defSccs :: Ord key => DefMap key def -> [ NAM.AdjacencyMap key ]
defSccs tds =
    let
        perKeyDeps = fmap (\(key, (_, deps)) -> (key, deps)) (Map.assocs tds)
        keySccs = AM.scc (AM.fromAdjacencySets perKeyDeps)
    -- the graph made by 'scc' is guaranteed to be acyclic
    in case AM.topSort keySccs of
        Right sorted -> sorted
        -- TODO: report cycle
        Left _       -> error "No topological sort of SCC graph"

wrapWithDefs
    :: Ord key
    => ann
    -> DefMap key (Binding tyname name uni fun ann)
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
wrapWithDefs x tds body =
    let toValue k = fst <$> Map.lookup k tds
        wrapDefScc acc scc =
            let bs = catMaybes $ toValue <$> Graph.vertexList scc
            in mkLet x (if Graph.isAcyclic scc then NonRec else Rec) bs acc
    -- process from the inside out
    in foldl' wrapDefScc body (defSccs tds)

class (Monad m, Ord key) => MonadDefs key uni fun ann m | m -> key uni fun ann where
    liftDef :: DefT key uni fun ann Identity a -> m a
    default liftDef :: (MonadDefs key uni fun ann n, MonadTrans t, t n ~ m) => DefT key uni fun ann Identity a -> m a
    liftDef = lift . liftDef

instance (Ord key, Monad m) => MonadDefs key uni fun ann (DefT key uni fun ann m) where
    liftDef = MM.hoist (pure . runIdentity)

instance MonadDefs key uni fun ann m => MonadDefs key uni fun ann (StateT s m)
instance MonadDefs key uni fun ann m => MonadDefs key uni fun ann (ExceptT e m)
instance MonadDefs key uni fun ann m => MonadDefs key uni fun ann (ReaderT r m)

instance MonadIO m => MonadIO (DefT key uni fun ann m) where
    liftIO = lift . liftIO

defineTerm :: MonadDefs key uni fun ann m => key -> TermDefWithStrictness uni fun ann -> Set.Set key -> m ()
defineTerm name def deps = liftDef $ DefT $ modify $ over termDefs $ Map.insert name (def, deps)

defineType :: MonadDefs key uni fun ann m => key -> TypeDef TyName uni ann -> Set.Set key -> m ()
defineType name def deps = liftDef $ DefT $ modify $ over typeDefs $ Map.insert name (def, deps)

defineDatatype
    :: forall key uni fun ann m . MonadDefs key uni fun ann m
    => key -> DatatypeDef TyName Name uni fun ann -> Set.Set key -> m ()
defineDatatype name def deps = liftDef $ DefT $ modify $ over datatypeDefs $ Map.insert name (def, deps)

recordAlias :: forall key uni fun ann m . MonadDefs key uni fun ann m => key -> m ()
recordAlias name = liftDef @key @uni @fun @ann $ DefT $ modify $ over aliases (Set.insert name)

lookupTerm :: (MonadDefs key uni fun ann m) => ann -> key -> m (Maybe (Term TyName Name uni fun ann))
lookupTerm x name = do
    DefState{_termDefs=ds,_aliases=as} <- liftDef $ DefT get
    pure $ case Map.lookup name ds of
        Just (def, _) | not (Set.member name as) -> Just $ mkVar x $ PLC.defVar def
        _                                        -> Nothing

lookupOrDefineTerm :: (MonadDefs key uni fun ann m) => ann -> key -> m (TermDefWithStrictness uni fun ann, Set.Set key) -> m (Term TyName Name uni fun ann)
lookupOrDefineTerm x name mdef = do
    mTerm <- lookupTerm x name
    case mTerm of
        Just t -> pure t
        Nothing -> do
            (def, deps) <- mdef
            defineTerm name def deps
            pure $ mkVar x $ PLC.defVar def

lookupType :: (MonadDefs key uni fun ann m) => ann -> key -> m (Maybe (Type TyName uni ann))
lookupType x name = do
    DefState{_typeDefs=tys, _datatypeDefs=dtys, _aliases=as} <- liftDef $ DefT get
    pure $ case Map.lookup name tys of
        Just (def, _) -> Just $ if Set.member name as then PLC.defVal def else mkTyVar x $ PLC.defVar def
        Nothing -> case Map.lookup name dtys of
            Just (def, _) -> Just $ mkTyVar x $ PLC.defVar def
            Nothing       -> Nothing

lookupOrDefineType :: (MonadDefs key uni fun ann m) => ann -> key -> m (TypeDef TyName uni ann, Set.Set key) -> m (Type TyName uni ann)
lookupOrDefineType x name mdef = do
    mTy <- lookupType x name
    case mTy of
        Just ty -> pure ty
        Nothing -> do
            (def, deps) <- mdef
            defineType name def deps
            pure $ mkTyVar x $ PLC.defVar def

lookupConstructors :: (MonadDefs key uni fun ann m) => ann -> key -> m (Maybe [Term TyName Name uni fun ann])
lookupConstructors x name = do
    ds <- liftDef $ DefT $ use datatypeDefs
    pure $ case Map.lookup name ds of
        Just (PLC.Def{PLC.defVal=(Datatype _ _ _ _ constrs)}, _) -> Just $ fmap (mkVar x) constrs
        Nothing                                                  -> Nothing

lookupDestructor
    :: forall key uni fun ann m . (MonadDefs key uni fun ann m)
    => ann -> key -> m (Maybe (Term TyName Name uni fun ann))
lookupDestructor x name = do
    ds <- liftDef @key @uni @fun @ann $ DefT $ use datatypeDefs
    pure $ case Map.lookup name ds of
        Just (PLC.Def{PLC.defVal=(Datatype _ _ _ destr _)}, _) -> Just $ Var x destr
        Nothing                                                -> Nothing
