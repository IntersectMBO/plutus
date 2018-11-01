{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs     #-}
{-# LANGUAGE LambdaCase       #-}

module Language.PlutusCore.Clone (Cloneable(..), CloneWhat(..), cloneQuote, alphaRename, globalRename
                                 ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Control.Monad.State

import qualified Data.IntMap               as IM
import qualified Data.IntSet               as IS
import           Lens.Micro

type Cloning m = (MonadState CloneSt m, MonadQuote m)

-- | The currrent cloning state. As we go, we will make a mapping for each variable we are renaming to a fresh unique.
-- In addition, we keep track of the bound variables, so we can decide whether or not to rename them.
data CloneSt = CloneSt {
    csMapping :: IM.IntMap Unique -- ^ A mapping between uniques in the original program and renamed uniques.
    , csBound :: IS.IntSet -- ^ The set of bound variables seen so far.
    }

emptyState :: CloneSt
emptyState = CloneSt {csMapping=mempty, csBound=mempty}

addMapping :: Cloning m => Unique -> Unique -> m ()
addMapping (Unique oldU) newU = modify $ \(CloneSt mapping bound) -> CloneSt (IM.insert oldU newU mapping) bound

lookupMapping :: Cloning m => Unique -> m (Maybe Unique)
lookupMapping (Unique u) = do
    mapping <- gets csMapping
    pure $ IM.lookup u mapping

addBound :: Cloning m => Unique -> m ()
addBound (Unique u) = modify $ \(CloneSt mappings bound) -> CloneSt mappings (IS.insert u bound)

isBound :: Cloning m => Unique -> m Bool
isBound (Unique u) = IS.member u <$> gets csBound

shouldClone :: Cloning m => CloneWhat -> Unique -> m Bool
shouldClone what u = do
    bound <- isBound u
    pure $ case what of
        Bound -> bound
        All   -> True

data CloneWhat = Bound | All

-- | Get the renamed 'Unique' for an old 'Unique'.
getRenamed :: Cloning m => Unique -> m Unique
getRenamed oldU = do
    mapping <- lookupMapping oldU
    case mapping of
        Just newU -> pure newU
        Nothing   -> do
            newU <- liftQuote freshUnique
            addMapping oldU newU
            pure newU

cloneQuote :: (MonadQuote m, Cloneable a) => CloneWhat -> a -> m a
cloneQuote what = flip evalStateT emptyState . clone what

-- | Alpha rename the given 'Cloneable' (i.e. rename bound variables to be fresh).
alphaRename :: (MonadQuote m, Cloneable a) => a -> m a
alphaRename = cloneQuote Bound

-- | Rename all variables.
globalRename :: (MonadQuote m, Cloneable a) => a -> m a
globalRename = cloneQuote All

-- | A class for types which can be cloned, with control over which kinds of variables are cloned.
class Cloneable a where
    clone :: Cloning m => CloneWhat -> a -> m a

instance Cloneable Unique where
    clone what oldU = do
        doClone <- shouldClone what oldU

        if doClone
        then getRenamed oldU
        else pure oldU

instance Cloneable (Name a) where
    clone what n = do
        newU <- clone what $ nameUnique n
        pure $ n & unique .~ newU

instance Cloneable (TyName a) where
    clone what (TyName n) = TyName <$> clone what n

instance Cloneable (TyNameWithKind a) where
    clone what (TyNameWithKind n) = TyNameWithKind <$> clone what n

instance (Cloneable (tyname a), HasUnique (tyname a)) => Cloneable (Type tyname a) where
    clone what = \case
        TyVar a n          -> TyVar a <$> clone what n
        TyIFix a pat arg   -> TyIFix a <$> clone what pat <*> clone what arg
        TyForall a tn k ty -> do
            addBound (tn ^. unique)
            tn' <- clone what tn
            TyForall a tn' k <$> clone what ty
        TyLam a tn k ty    -> do
            addBound (tn ^. unique)
            tn' <- clone what tn
            TyLam a tn' k <$> clone what ty
        TyFun a t1 t2       -> TyFun a <$> clone what t1 <*> clone what t2
        TyApp a t1 t2       -> TyApp a <$> clone what t1 <*> clone what t2
        x                   -> pure x

instance (Cloneable (tyname a), Cloneable (name a), HasUnique (tyname a), HasUnique (name a)) => Cloneable (Term tyname name a) where
    clone what = \case
        Var a n           -> Var a <$> clone what n
        TyAbs a tn k ty   -> do
            addBound (tn ^. unique)
            tn' <- clone what tn
            TyAbs a tn' k <$> clone what ty
        LamAbs a n ty t   -> do
            addBound (n ^. unique)
            LamAbs a <$> clone what n <*> clone what ty <*> clone what t
        IWrap a pat arg t -> IWrap a <$> clone what pat <*> clone what arg <*> clone what t
        TyInst a x ty     -> TyInst a <$> clone what x <*> clone what ty
        Error a ty        -> Error a <$> clone what ty
        Apply a t1 t2     -> Apply a <$> clone what t1 <*> clone what t2
        Unwrap a t        -> Unwrap a <$> clone what t
        x                 -> pure x

instance (Cloneable (tyname a), Cloneable (name a), HasUnique (tyname a), HasUnique (name a)) => Cloneable (Program tyname name a) where
    clone what (Program a v t) = Program a v <$> clone what t
