{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
-- just for the type equality constraint
{-# LANGUAGE GADTs                 #-}

module Language.PlutusCore.Quote
    ( runQuoteT
    , runQuote
    , freshUnique
    , freshName
    , freshTyName
    , freshenName
    , freshenTyName
    , QuoteT (..)
    , Quote
    , MonadQuote
    , FreshState
    , liftQuote
    , markNonFreshBelow
    , markNonFresh
    , markNonFreshMax
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Name

import           Control.Monad.Except
import           Control.Monad.Morph       as MM
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Functor.Identity
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import qualified Data.Text                 as Text
import           Hedgehog                  (GenT, PropertyT)

-- | The state contains the "next" 'Unique' that should be used for a name
type FreshState = Unique

emptyFreshState :: FreshState
emptyFreshState = Unique 0

-- | The "quotation" monad transformer. Within this monad you can do safe construction of PLC terms using quasiquotation,
-- fresh-name generation, and parsing.
newtype QuoteT m a = QuoteT { unQuoteT :: StateT FreshState m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadError e, MonadReader r, MonadIO)

-- Need to write this by hand, deriving wants to derive the one for DefState
instance MonadState s m => MonadState s (QuoteT m) where
    get = lift get
    put = lift . put
    state = lift . state

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
runQuoteT ::  Monad m => QuoteT m a -> m a
runQuoteT q = evalStateT (unQuoteT q) emptyFreshState

-- | A non-transformer version of 'QuoteT'.
type Quote = QuoteT Identity

-- | See 'runQuoteT'.
runQuote :: Quote a -> a
runQuote = runIdentity . runQuoteT

-- | Get a fresh 'Unique'.
freshUnique :: MonadQuote m => m Unique
freshUnique = liftQuote $ do
    nextU <- QuoteT get
    QuoteT $ put $ Unique (unUnique nextU + 1)
    pure nextU

-- | Get a fresh 'Name', given the annotation and the 'Text.Text' name.
freshName :: MonadQuote m => Text.Text -> m Name
freshName str = Name str <$> freshUnique

-- | Make a copy of the given 'Name' that is distinct from the old one.
freshenName :: MonadQuote m => Name -> m Name
freshenName (Name str _) = Name str <$> freshUnique

-- | Get a fresh 'TyName', given the annotation and the 'Text.Text' name.
freshTyName :: MonadQuote m => Text.Text -> m TyName
freshTyName = fmap TyName <$> freshName

-- | Make a copy of the given 'TyName' that is distinct from the old one.
freshenTyName :: MonadQuote m => TyName -> m TyName
freshenTyName (TyName name) = TyName <$> freshenName name

-- | Mark a all 'Unique's less than the given 'Unique' as used, so they will not be generated in future.
markNonFreshBelow :: MonadQuote m => Unique -> m ()
markNonFreshBelow = liftQuote . QuoteT . modify . max

-- | Mark a given 'Unique' (and implicitly all 'Unique's less than it) as used, so they will not be generated in future.
markNonFresh :: MonadQuote m => Unique -> m ()
markNonFresh = markNonFreshBelow . succ

-- | Mark the maximal 'Unique' from a set of 'Unique's (and implicitly all 'Unique's less than it)
-- as used, so they will not be generated in future.
markNonFreshMax :: MonadQuote m => Set Unique -> m ()
markNonFreshMax = markNonFresh . fromMaybe (Unique 0) . Set.lookupMax
