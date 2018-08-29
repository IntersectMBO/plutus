{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}

module Language.PlutusCore.Quote (
              runQuoteT
            , runQuote
            , freshUnique
            , freshName
            , freshTyName
            , parseProgram
            , parseTerm
            , parseType
            , annotateProgram
            , annotateTerm
            , typecheckProgram
            , typecheckTerm
            , QuoteT
            , Quote
            ) where

import           Control.Monad.Except
import           Control.Monad.Morph               as MM
import           Control.Monad.State

import qualified Data.ByteString.Lazy              as BSL
import           Data.Functor.Identity
import qualified Data.IntMap                       as IM

import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer         (AlexPosn)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parser        (ParseError, parseST, parseTermST, parseTypeST)
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis
import           PlutusPrelude

-- | The state contains the "next" 'Unique' that should be used for a name
type FreshState = Unique

emptyFreshState :: FreshState
emptyFreshState = Unique 0

-- | The "quotation" monad transformer. Within this monad you can do safe construction of PLC terms using quasiquotation,
-- fresh-name generation, and parsing.
newtype QuoteT m a = QuoteT { unQuoteT :: StateT FreshState m a }
    -- the MonadState constraint is handy, but it's useless outside since we don't export the state type
    deriving (Functor, Applicative, Monad, MonadTrans, MM.MFunctor, MonadState FreshState)

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

-- | Get a fresh 'TyName', given the annotation an the name.
freshTyName :: (Monad m) => a -> BSL.ByteString -> QuoteT m (TyName a)
freshTyName = fmap TyName .* freshName

mapParseRun :: (MonadError Error m) => StateT IdentifierState (Except ParseError) a -> QuoteT m a
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = MM.hoist (liftEither . convertError . runExcept) $ QuoteT $ StateT $ \nextU -> do
    (p, (_, _, u)) <- runStateT run (identifierStateFrom nextU)
    pure (p, u)

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (MonadError Error m) => BSL.ByteString -> QuoteT m (Program TyName Name AlexPosn)
parseProgram str = mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (MonadError Error m) => BSL.ByteString -> QuoteT m (Term TyName Name AlexPosn)
parseTerm str = mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (MonadError Error m) => BSL.ByteString -> QuoteT m (Type TyName AlexPosn)
parseType str = mapParseRun (parseTypeST str)

-- | Annotate a PLC program, so that all names are annotated with their types/kinds.
annotateProgram :: (MonadError Error m) => Program TyName Name AlexPosn -> QuoteT m (Program TyNameWithKind NameWithType AlexPosn)
annotateProgram (Program a v t) = Program a v <$> annotateTerm t

-- | Annotate a PLC term, so that all names are annotated with their types/kinds.
annotateTerm :: (MonadError Error m) => Term TyName Name AlexPosn -> QuoteT m (Term TyNameWithKind NameWithType AlexPosn)
annotateTerm t = do
  (ts, t') <- (lift . liftEither . convertError) (annotateTermST t)
  updateMaxU ts
  pure t'
      where
          updateMaxU :: (Monad m) => TypeState a -> QuoteT m ()
          updateMaxU (TypeState _ tys) = do
              nextU <- get
              let tsMaxU = maybe 0 (fst . fst) (IM.maxViewWithKey tys)
              let maxU = unUnique nextU - 1
              put $ Unique $ max maxU tsMaxU

-- | Typecheck a PLC program.
typecheckProgram :: (MonadError Error m) => Natural -> Program TyNameWithKind NameWithType AlexPosn -> QuoteT m (Type TyNameWithKind ())
typecheckProgram n (Program _ _ t) = typecheckTerm n t

-- | Typecheck a PLC term.
typecheckTerm :: (MonadError Error m) => Natural -> Term TyNameWithKind NameWithType AlexPosn -> QuoteT m (Type TyNameWithKind ())
typecheckTerm n t = do
  nextU <- get
  let maxU = unUnique nextU - 1
  (lift . liftEither . convertError) (runTypeCheckM maxU n (typeOf t))
