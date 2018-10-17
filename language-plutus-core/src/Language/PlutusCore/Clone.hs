{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs     #-}
{-# LANGUAGE LambdaCase       #-}

module Language.PlutusCore.Clone (Cloneable(..), CloneWhat(..), cloneQuote, alphaRename, globalRename
                                 ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Foldable
import           Data.Functor.Foldable
import qualified Data.IntMap               as IM
import qualified Data.IntSet               as IS
import qualified Data.List.NonEmpty        as NE
import           Data.Maybe                (fromMaybe)
import           Lens.Micro

type Cloning m = (MonadState CloneSt m, MonadReader CloneWhat m, MonadQuote m)

data CloneSt = CloneSt {
    csMappingStack :: NE.NonEmpty (IM.IntMap Unique) -- ^ A scoped stack of unique mappings.
    , csBound      :: IS.IntSet -- ^ The set of bound variables seen so far.
    }

emptyState :: CloneSt
emptyState = CloneSt {csMappingStack=mempty NE.:| [], csBound=mempty}

addMapping :: Cloning m => Int -> Unique -> m ()
addMapping oldU newU = modify $ \(CloneSt (top NE.:| rest) bound) -> CloneSt (IM.insert oldU newU top NE.:| rest) bound

lookupMapping :: Cloning m => Unique -> m (Maybe Unique)
lookupMapping (Unique u) = do
    mappings <- gets csMappingStack
    pure $ foldl' (<|>) Nothing (fmap (IM.lookup u) mappings)

-- | Run the given action with an additional scope popped on the stack, and then pop it off afterwards.
withScope :: Cloning m => m a -> m a
withScope act = do
    modify $ \(CloneSt mappings bound) -> CloneSt (mempty NE.<| mappings) bound
    a <- act
    modify $ \(CloneSt (_ NE.:| rest) bound) -> CloneSt (fromMaybe (mempty NE.:| []) (NE.nonEmpty rest)) bound
    pure a

addBound :: Cloning m => Unique -> m ()
addBound u@(Unique i) = do
    modify $ \(CloneSt mappings bound) -> CloneSt mappings (IS.insert i bound)
    -- if we are cloning bound variables then we should make sure that we make a fresh
    -- mapping for this variable, even if it already appears in the mappings, since there
    -- might be name shadowing
    doClone <- shouldClone u
    when doClone (void $ freshenUnique u)

isBound :: Cloning m => Unique -> m Bool
isBound (Unique u) = IS.member u <$> gets csBound

shouldClone :: Cloning m => Unique -> m Bool
shouldClone u = do
    bound <- isBound u
    what <- ask
    pure $ if bound then cloneBound what else cloneFree what

data CloneWhat = Bound | Free | Both

cloneBound :: CloneWhat -> Bool
cloneBound = \case
    Bound -> True
    Free -> False
    Both -> True

cloneFree :: CloneWhat -> Bool
cloneFree = \case
    Bound -> False
    Free -> True
    Both -> True

freshenUnique :: Cloning m => Unique -> m Unique
freshenUnique (Unique oldU) = do
    newU <- liftQuote freshUnique
    addMapping oldU newU
    pure newU

cloneQuote :: (MonadQuote m, Cloneable a) => CloneWhat -> a -> m a
cloneQuote what = flip runReaderT what . flip evalStateT emptyState . clone

-- | Alpha rename the given 'Cloneable' (i.e. rename bound variables to be fresh).
alphaRename :: (MonadQuote m, Cloneable a) => a -> m a
alphaRename = cloneQuote Bound

-- | Rename all variables to be globally unique. Handles non-uniqueness in different scopes and shadowing.
globalRename :: (MonadQuote m, Cloneable a) => a -> m a
globalRename = cloneQuote Both

-- | A class for types which can be cloned, with control over which kinds of variables are cloned.
class Cloneable a where
    clone :: Cloning m => a -> m a

instance Cloneable Unique where
    clone oldU = do
        doClone <- shouldClone oldU

        if doClone
        then do
            mapping <- lookupMapping oldU
            case mapping of
                Just newU -> pure newU
                Nothing   -> freshenUnique oldU
        else pure oldU

instance Cloneable (Name a) where
    clone n = do
        newU <- clone $ nameUnique n
        pure $ n & unique .~ newU

instance Cloneable (TyName a) where
    clone (TyName n) = TyName <$> clone n

instance Cloneable (TyNameWithKind a) where
    clone (TyNameWithKind n) = TyNameWithKind <$> clone n

instance (Cloneable (tyname a), HasUnique (tyname a)) => Cloneable (Type tyname a) where
    clone = cata f where
        f = \case
            TyVarF a n          -> TyVar a <$> clone n
            TyFixF a tn ty      -> withScope $ do
                addBound (tn ^. unique)
                TyFix a <$> clone tn <*> ty
            TyForallF a tn k ty -> withScope $ do
                addBound (tn ^. unique)
                tn' <- clone tn
                TyForall a tn' k <$> ty
            TyLamF a tn k ty    -> withScope $ do
                addBound (tn ^. unique)
                tn' <- clone tn
                TyLam a tn' k <$> ty
            x                   -> embed <$> sequence x

instance (Cloneable (tyname a), Cloneable (name a), HasUnique (tyname a), HasUnique (name a)) => Cloneable (Term tyname name a) where
    clone = cata f where
        f = \case
            VarF a n         -> Var a <$> clone n
            TyAbsF a tn k ty -> withScope $ do
                addBound (tn ^. unique)
                tn' <- clone tn
                TyAbs a tn' k <$> ty
            LamAbsF a n ty t -> withScope $ do
                addBound (n ^. unique)
                LamAbs a <$> clone n <*> clone ty <*> t
            WrapF a tn ty t  -> withScope $ do
                addBound (tn ^. unique)
                Wrap a <$> clone tn <*> clone ty <*> t
            TyInstF a x ty   -> TyInst a <$> x <*> clone ty
            ErrorF a ty      -> Error a <$> clone ty
            x                -> embed <$> sequence x

instance (Cloneable (tyname a), Cloneable (name a), HasUnique (tyname a), HasUnique (name a)) => Cloneable (Program tyname name a) where
    clone (Program a v t) = Program a v <$> clone t
