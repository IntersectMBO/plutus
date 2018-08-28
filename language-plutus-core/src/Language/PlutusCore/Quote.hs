{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.Quote (
              runQuoteT
            , runQuote
            , freshUnique
            , freshName
            , freshTyName
            , parseProgram
            , parseTerm
            , parseType
            , QuoteT
            , Quote
            ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Morph        as MM
import qualified Data.ByteString.Lazy       as BSL
import           Language.PlutusCore.Lexer  (AlexPosn)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parser (ParseError, parseST, parseTermST, parseTypeST)
import           Language.PlutusCore.Type
import           Data.Functor.Identity
import           PlutusPrelude

-- | The state contains the "next" 'Unique' that should be used for a name
type FreshState = Unique

emptyFreshState :: FreshState
emptyFreshState = Unique 0

-- | The "quotation" monad transformer. This allows creation of fresh names and parsing.
newtype QuoteT m a = QuoteT { unQuoteT :: StateT FreshState m a }
    -- the MonadState constraint is handy, but it's useless outside since we don't export the state type
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadState FreshState)

-- | Run a quote from an empty identifier state. Note that the resulting term cannot necessarily
-- be safely combined with other terms - that should happen inside 'QuoteT'.
runQuoteT ::  (Monad m) => QuoteT m a -> m a
runQuoteT q = evalStateT (unQuoteT q) emptyFreshState

-- | A non-transformer version of 'QuoteT'.
type Quote a = QuoteT Identity a

-- | See 'runQuoteT'.
runQuote :: Quote a -> a
runQuote = runIdentity . runQuoteT

-- | Get a fresh 'Unique'.
freshUnique :: (Monad m) => QuoteT m Unique
freshUnique = do
    nextU <- get
    put $ Unique ((unUnique nextU) + 1)
    pure $ nextU

-- | Get a fresh 'Name', given the annotation an the name.
freshName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (Name a)
freshName ann str = Name ann str <$> freshUnique

-- | Get a fresh 'TyName', given the annotation an the name.
freshTyName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (TyName a)
freshTyName = fmap TyName .* freshName

mapParseRun :: (MonadError ParseError m) => StateT IdentifierState (Except ParseError) a -> QuoteT m a
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = MM.hoist (liftEither . runExcept) $ QuoteT $ StateT $ \nextU -> do
    (p, (_, _, u)) <- runStateT run (identifierStateFrom nextU)
    pure $ (p, u)

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (MonadError ParseError m) => BSL.ByteString -> QuoteT m (Program TyName Name AlexPosn)
parseProgram str = mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (MonadError ParseError m) => BSL.ByteString -> QuoteT m (Term TyName Name AlexPosn)
parseTerm str = mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (MonadError ParseError m) => BSL.ByteString -> QuoteT m (Type TyName AlexPosn)
parseType str = mapParseRun (parseTypeST str)
