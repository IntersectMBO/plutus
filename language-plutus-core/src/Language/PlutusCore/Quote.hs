{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
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
            , withTerm
            , withType
            , QuoteT
            , Quote
            , MonadQuote
            , FreshState
            , liftQuote
            , convertErrors
            ) where

import           Control.Monad.Except
import           Control.Monad.Morph       as MM
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.ByteString.Lazy      as BSL
import           Data.Functor.Identity
import           Hedgehog                  (GenT)

import           Language.PlutusCore.MkPlc
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
instance MonadQuote m => MonadQuote (ExceptT e m)
instance MonadQuote m => MonadQuote (ReaderT r m)
instance MonadQuote m => MonadQuote (GenT m)

-- | Map the errors in a 'MonadError' and 'MonadQuote' context according to the given function.
-- This can be used on the functions exported from this module to change the error type.
convertErrors :: forall a b m o .
  (MonadError b m, MonadQuote m)
  => (a -> b)
  -> ExceptT a Quote o
  -> m o
convertErrors convert act = (liftEither . first convert) =<< (liftQuote $ runExceptT act)

-- | Run a quote from an empty identifier state. Note that the resulting term cannot necessarily
-- be safely combined with other terms - that should happen inside 'QuoteT'.
runQuoteT ::  (Monad m) => QuoteT m a -> m a
runQuoteT q = evalStateT (unQuoteT q) emptyFreshState

-- | A non-transformer version of 'QuoteT'.
type Quote = QuoteT Identity

-- | See 'runQuoteT'.
runQuote :: Quote a -> a
runQuote = runIdentity . runQuoteT

-- | Get a fresh 'Unique'.
freshUnique :: (Monad m) => QuoteT m Unique
freshUnique = do
    nextU <- get
    put $ Unique (unUnique nextU + 1)
    pure nextU

-- | Get a fresh 'Name', given the annotation an the name.
freshName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (Name a)
freshName ann str = Name ann str <$> freshUnique

-- | Make a copy of the given 'Name' that is distinct from the old one.
freshenName :: (Monad m) =>  Name a -> QuoteT m (Name a)
freshenName (Name ann str _) = Name ann str <$> freshUnique

-- | Get a fresh 'TyName', given the annotation an the name.
freshTyName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (TyName a)
freshTyName = fmap TyName .* freshName

-- | Make a copy of the given 'TyName' that is distinct from the old one.
freshenTyName :: (Monad m) =>  TyName a -> QuoteT m (TyName a)
freshenTyName (TyName name) = TyName <$> freshenName name

-- | Make a term available under a given name inside a computation.
withTerm :: (MonadQuote m) => m (Term TyName Name ()) -> m (Type TyName ()) -> m (Name ()) -> (Name () -> m (Term TyName Name ())) -> m (Term TyName Name ())
withTerm bindM tyM n f = do
    name <- n
    mkTermLet name <$> bindM <*> tyM <*> f name

-- | Make a type available under a given name inside a computation. Note: the result of the computation must be a value.
withType :: (MonadQuote m) => m (Type TyName ()) -> m (Kind ()) -> m (TyName ()) -> (TyName () -> m (Term TyName Name ())) -> m (Term TyName Name ())
withType bindM kM n f = do
    name <- n
    mkTypeLet name <$> bindM <*> kM <*> f name
