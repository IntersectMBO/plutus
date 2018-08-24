{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExplicitForAll             #-}
{-# LANGUAGE Rank2Types                 #-}

module Language.PlutusCore.Quote (
              runQuoteT
            , runQuote
            , freshName
            , freshTyName
            , parse
            , QuoteT
            , Quote
            ) where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.ByteString.Lazy       as BSL
import           Language.PlutusCore.Lexer  (AlexPosn)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parser (ParseError, parseST)
import           Language.PlutusCore.Type
import           Data.Functor.Identity
import           PlutusPrelude

type FreshState = Unique

emptyFreshState :: FreshState
emptyFreshState = Unique 0

-- | The "quotation" monad transformer. This allows creation of fresh names and parsing.
newtype QuoteT m a = QuoteT { unQuoteT :: StateT FreshState m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MonadState FreshState)

-- | Run a quote from an empty identifier state. Note that the resulting term cannot necessarily
-- be safely combined with other terms - that should happen inside 'QuoteT'.
runQuoteT ::  (Monad m) => QuoteT m a -> m a
runQuoteT q = evalStateT (unQuoteT q) emptyFreshState

-- | A non-transformer version of 'QuoteT'.
type Quote a = QuoteT Identity a

-- | See 'runQuoteT'.
runQuote :: Quote a -> a
runQuote = runIdentity . runQuoteT

-- this is like a slightly restricted version of 'mapStateT' that doesn't reveal that it's a state monad
-- | Given a natural transformation on the internal monad, maps it over a 'QuoteT'. Useful for e.g. swapping
-- out inner error-handling monads.
mapInner :: (forall b. m b -> n b) -> QuoteT m a -> QuoteT n a
mapInner f = QuoteT . mapStateT f . unQuoteT

freshName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (Name a)
freshName ann str = do
    nextU <- get
    put $ Unique ((unUnique nextU) + 1)
    pure $ Name ann str nextU

freshTyName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (TyName a)
freshTyName = fmap TyName .* freshName

parse :: (MonadError ParseError m) => BSL.ByteString -> QuoteT m (Program TyName Name AlexPosn)
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
parse str = mapInner (liftEither . runExcept) $ QuoteT $ StateT $ \nextU -> do
    (p, (_, _, u)) <- runStateT (parseST str) (identifierStateFrom nextU)
    pure $ (p, u)
