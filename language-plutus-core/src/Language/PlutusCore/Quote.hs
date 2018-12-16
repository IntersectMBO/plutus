{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- just for the type equality constraint
{-# LANGUAGE GADTs                 #-}

module Language.PlutusCore.Quote (
              runQuoteT
            , runQuote
            , freshUnique
            , freshName
            , freshTyName
            , freshenName
            , freshenTyName
            , markNonFresh
            , markNonFreshTerm
            , markNonFreshType
            , markNonFreshProgram
            , QuoteT
            , Quote
            , MonadQuote
            , FreshState
            , liftQuote
            ) where

import           Control.Lens              (coerced)
import           Control.Monad.Except
import           Control.Monad.Morph       as MM
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe

import qualified Data.ByteString.Lazy      as BSL
import           Data.Functor.Foldable
import           Data.Functor.Identity
import qualified Data.Set                  as Set
import           Hedgehog                  (GenT, PropertyT)

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | The state contains the "next" 'Unique' that should be used for a name
type FreshState = Unique

emptyFreshState :: FreshState
emptyFreshState = Unique 0

-- | The "quotation" monad transformer. Within this monad you can do safe construction of PLC terms using quasiquotation,
-- fresh-name generation, and parsing.
newtype QuoteT m a = QuoteT { unQuoteT :: StateT FreshState m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadState FreshState, MonadError e, MonadReader r)

-- | A monad that allows lifting of quoted expressions.
class Monad m => MonadQuote m where
    liftQuote :: Quote a -> m a
    -- This means we don't have to implement it when we're writing an instance for a MonadTrans monad. We can't just
    -- add an instance declaration for that, because it overlaps with the base instance.
    default liftQuote :: (MonadQuote n, MonadTrans t, t n ~ m) => Quote a -> m a
    liftQuote = lift . liftQuote

instance (Monad m) => MonadQuote (QuoteT m) where
    liftQuote = MM.hoist (pure . runIdentity)

instance MonadQuote m => MonadQuote (StateT s m)
instance MonadQuote m => MonadQuote (MaybeT m)
instance MonadQuote m => MonadQuote (ExceptT e m)
instance MonadQuote m => MonadQuote (ReaderT r m)
instance MonadQuote m => MonadQuote (GenT m)
instance MonadQuote m => MonadQuote (PropertyT m)

-- | Run a quote from an empty identifier state. Note that the resulting term cannot necessarily
-- be safely combined with other terms - that should happen inside 'QuoteT'.
runQuoteT ::  (Monad m) => QuoteT m a -> m a
runQuoteT q = evalStateT (unQuoteT q) emptyFreshState

-- | A non-transformer version of 'QuoteT'.
type Quote = QuoteT Identity

-- | See 'runQuoteT'.
runQuote :: Quote a -> a
runQuote = runIdentity . runQuoteT

-- | Marks all the 'Unique's in a type as used, so they will not be generated in future. Useful if you
-- have a type which was not generated in 'Quote'.
markNonFreshType
    :: (HasUnique (tyname a) TypeUnique, MonadQuote m)
    => Type tyname a
    -> m ()
markNonFreshType = markNonFresh . maximum . collectTypeUniques

-- | Marks all the 'Unique's in a term as used, so they will not be generated in future. Useful if you
-- have a term which was not generated in 'Quote'.
markNonFreshTerm
    :: (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique, MonadQuote m)
    => Term tyname name a
    -> m ()
markNonFreshTerm = markNonFresh . maximum . collectTermUniques

-- | Marks all the 'Unique's in a program as used, so they will not be generated in future. Useful if you
-- have a program which was not generated in 'Quote'.
markNonFreshProgram
    :: (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique, MonadQuote m)
    => Program tyname name a
    -> m ()
markNonFreshProgram (Program _ _ body)= markNonFreshTerm body

-- | Mark a given 'Unique' (and implicitly all 'Unique's less than it) as used, so they will not be generated in future.
markNonFresh :: MonadQuote m => Unique -> m ()
markNonFresh nonFresh = liftQuote $ do
    nextU <- get
    put $ Unique (max (unUnique nonFresh + 1) (unUnique nextU))

collectTypeUniques :: (HasUnique (tyname a) TypeUnique) => Type tyname a -> Set.Set Unique
collectTypeUniques = cata f where
    f = \case
        TyVarF _ tn        -> Set.singleton (tn ^. unique . coerced)
        TyFixF _ tn t      -> Set.insert (tn ^. unique . coerced) t
        TyForallF _ tn _ t -> Set.insert (tn ^. unique . coerced) t
        TyLamF _ tn _ t    -> Set.insert (tn ^. unique . coerced) t
        TyAppF _ t1 t2     -> t1 <> t2
        TyFunF _ t1 t2     -> t1 <> t2
        _                  -> mempty

collectTermUniques :: (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique) => Term tyname name a -> Set.Set Unique
collectTermUniques = cata f where
    f = \case
        VarF _ n         -> Set.singleton (n ^. unique . coerced)
        LamAbsF _ n ty t -> Set.insert (n ^. unique . coerced) (collectTypeUniques ty <> t)
        WrapF _ tn ty t  -> Set.insert (tn ^. unique . coerced) (collectTypeUniques ty <> t)
        TyAbsF _ tn _ t  -> Set.insert (tn ^. unique . coerced) t
        TyInstF _ t ty   -> t <> collectTypeUniques ty
        ApplyF _ t1 t2   -> t1 <> t2
        UnwrapF _ t      -> t
        ErrorF _ ty      -> collectTypeUniques ty
        _                -> mempty

-- | Get a fresh 'Unique'.
freshUnique :: MonadQuote m => m Unique
freshUnique = liftQuote $ do
    nextU <- get
    put $ Unique (unUnique nextU + 1)
    pure nextU

-- | Get a fresh 'Name', given the annotation an the name.
freshName :: Monad m => a -> BSL.ByteString -> QuoteT m (Name a)
freshName ann str = Name ann str <$> freshUnique

-- | Make a copy of the given 'Name' that is distinct from the old one.
freshenName :: Monad m =>  Name a -> QuoteT m (Name a)
freshenName (Name ann str _) = Name ann str <$> freshUnique

-- | Get a fresh 'TyName', given the annotation an the name.
freshTyName :: Monad m => a -> BSL.ByteString -> QuoteT m (TyName a)
freshTyName = fmap TyName .* freshName

-- | Make a copy of the given 'TyName' that is distinct from the old one.
freshenTyName :: Monad m =>  TyName a -> QuoteT m (TyName a)
freshenTyName (TyName name) = TyName <$> freshenName name
