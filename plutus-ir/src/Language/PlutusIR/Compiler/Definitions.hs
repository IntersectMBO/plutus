{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}
-- | Support for generating PIR with global definitions with dependencies between them.
module Language.PlutusIR.Compiler.Definitions (DefT
                                              , MonadDefs (..)
                                              , runDefT
                                              , defineTerm
                                              , defineType
                                              , defineDatatype
                                              , recordAlias
                                              , lookupType
                                              , lookupTerm
                                              , lookupConstructors
                                              , lookupDestructor) where

import           Language.PlutusIR
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore.MkPlc as PLC
import           Language.PlutusCore.Quote

import           Control.Lens
import           Control.Monad.Except
import qualified Control.Monad.Morph       as MM
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Foldable
import qualified Data.Graph                as Graph
import qualified Data.Map                  as Map
import qualified Data.Set                  as Set

-- | A map from keys to pairs of bindings and their dependencies (as a list of keys).
type DefMap key def = Map.Map key (def, Set.Set key)

mapDefs :: (a -> b) -> DefMap key a -> DefMap key b
mapDefs f = Map.map (\(def, deps) -> (f def, deps))

data DefState key ann = DefState {
    _termDefs     :: DefMap key (TermDef TyName Name ann),
    _typeDefs     :: DefMap key (TypeDef TyName ann),
    _datatypeDefs :: DefMap key (DatatypeDef TyName Name ann),
    _aliases      :: Set.Set key
    }
makeLenses ''DefState

newtype DefT key ann m a = DefT { unDefT :: StateT (DefState key ann) m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadState (DefState key ann), MonadError e, MonadReader r, MonadQuote)

-- TODO: provenances
runDefT :: (Monad m, Ord key) => ann -> DefT key ann m (Term TyName Name ann) -> m (Term TyName Name ann)
runDefT x act = do
    (term, s) <- runStateT (unDefT act) (DefState mempty mempty mempty mempty)
    let wrapped = wrapWithDefs x (bindingDefs s) term
    pure wrapped
        where
            bindingDefs defs =
                let
                    terms = mapDefs (\d -> TermBind x (PLC.defVar d) (PLC.defVal d)) (_termDefs defs)
                    types = mapDefs (\d -> TypeBind x (PLC.defVar d) (PLC.defVal d)) (_typeDefs defs)
                    datatypes = mapDefs (\d -> DatatypeBind x (PLC.defVal d)) (_datatypeDefs defs)
                in terms `Map.union` types `Map.union` datatypes

-- | Given the definitions in the program, create a topologically ordered list of the SCCs using the dependency information
defSccs :: Ord key => DefMap key def -> [Graph.SCC def]
defSccs tds =
    let
        inputs = fmap (\(key, (d, deps)) -> (d, key, Set.toList deps)) (Map.assocs tds)
    in
        Graph.stronglyConnComp inputs

wrapWithDefs
    :: Ord key
    => ann
    -> DefMap key (Binding TyName Name ann)
    -> Term TyName Name ann
    -> Term TyName Name ann
wrapWithDefs x tds body =
    let
        sccs = defSccs tds
        wrapDefScc acc scc = case scc of
            Graph.AcyclicSCC def -> Let x NonRec [ def ] acc
            Graph.CyclicSCC ds   -> Let x Rec ds acc
    in
        -- process from the inside out
        foldl' wrapDefScc body (reverse sccs)

class (Monad m, Ord key) => MonadDefs key ann m | m -> key where
    liftDef :: DefT key ann Identity a -> m a
    default liftDef :: (MonadDefs key ann n, MonadTrans t, t n ~ m) => DefT key ann Identity a -> m a
    liftDef = lift . liftDef

instance (Ord key, Monad m) => MonadDefs key ann (DefT key ann m) where
    liftDef = MM.hoist (pure . runIdentity)

instance MonadDefs key ann m => MonadDefs key ann (StateT s m)
instance MonadDefs key ann m => MonadDefs key ann (ExceptT e m)
instance MonadDefs key ann m => MonadDefs key ann (ReaderT r m)

defineTerm :: MonadDefs key ann m => key -> TermDef TyName Name ann -> Set.Set key -> m ()
defineTerm name def deps = liftDef $ modify $ over termDefs $ Map.insert name (def, deps)

defineType :: MonadDefs key ann m => key -> TypeDef TyName ann -> Set.Set key -> m ()
defineType name def deps = liftDef $ modify $ over typeDefs $ Map.insert name (def, deps)

defineDatatype :: forall key ann m . MonadDefs key ann m => key -> DatatypeDef TyName Name ann -> Set.Set key -> m ()
defineDatatype name def deps = liftDef $ modify $ over datatypeDefs $ Map.insert name (def, deps)

recordAlias :: forall key ann m . MonadDefs key ann m => key -> m ()
recordAlias name = liftDef @key @ann $ modify $ over aliases (Set.insert name)

lookupType :: (MonadDefs key ann m) => ann -> key -> m (Maybe (Type TyName ann))
lookupType x name = do
    DefState{_typeDefs=tys, _datatypeDefs=dtys, _aliases=as} <- liftDef get
    pure $ case Map.lookup name tys of
        Just (def, _) -> Just $ if Set.member name as then PLC.defVal def else mkTyVar x $ PLC.defVar def
        Nothing -> case Map.lookup name dtys of
            Just (def, _) -> Just $ mkTyVar x $ PLC.defVar def
            Nothing       -> Nothing

lookupTerm :: (MonadDefs key ann m) => ann -> key -> m (Maybe (Term TyName Name ann))
lookupTerm x name = do
    DefState{_termDefs=ds,_aliases=as} <- liftDef get
    pure $ case Map.lookup name ds of
        Just (def, _) -> Just $ if Set.member name as then PLC.defVal def else mkVar x $ PLC.defVar def
        Nothing       -> Nothing

lookupConstructors :: (MonadDefs key ann m) => ann -> key -> m (Maybe [Term TyName Name ann])
lookupConstructors x name = do
    ds <- liftDef $ use datatypeDefs
    pure $ case Map.lookup name ds of
        Just (PLC.Def{PLC.defVal=(Datatype _ _ _ _ constrs)}, _) -> Just $ fmap (mkVar x) constrs
        Nothing                                                  -> Nothing

lookupDestructor :: (MonadDefs key ann m) => ann -> key -> m (Maybe (Term TyName Name ann))
lookupDestructor x name = do
    ds <- liftDef $ use datatypeDefs
    pure $ case Map.lookup name ds of
        Just (PLC.Def{PLC.defVal=(Datatype _ _ _ destr _)}, _) -> Just $ Var x destr
        Nothing                                                -> Nothing
