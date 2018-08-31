{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
-- just for the type equality constraint
{-# LANGUAGE GADTs             #-}

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
            , MonadQuote
            , liftQuote
            , convertErrors
            ) where

import           Control.Monad.Except
import           Control.Monad.Morph               as MM
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.ByteString.Lazy              as BSL
import           Data.Functor.Identity
import qualified Data.IntMap                       as IM
import           Language.PlutusCore.Lexer         (AlexPosn)

import           Language.PlutusCore.Error
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

-- | Map the errors in a 'MonadError' and 'MonadQuote' context according to the given function.
-- This can be used on the functions exported from this module to change the error type.
convertErrors :: forall a b m o .
  (MonadError b m, MonadQuote m)
  => (a -> b)
  -> ExceptT a Quote o
  -> m o
convertErrors convert act = (liftEither . first convert) =<< (liftQuote $ runExceptT $ act)

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

mapParseRun :: (MonadError (Error a) m, MonadQuote m) => StateT IdentifierState (Except (ParseError a)) b -> m b
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = convertErrors asError $ do
    nextU <- liftQuote get
    (p, (_, _, u)) <- liftEither $ runExcept $ runStateT run (identifierStateFrom nextU)
    liftQuote $ put u
    pure p

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (MonadError (Error AlexPosn) m, MonadQuote m) => BSL.ByteString -> m (Program TyName Name AlexPosn)
parseProgram str = mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (MonadError (Error AlexPosn) m, MonadQuote m) => BSL.ByteString -> m (Term TyName Name AlexPosn)
parseTerm str = mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (MonadError (Error AlexPosn) m, MonadQuote m) => BSL.ByteString -> m (Type TyName AlexPosn)
parseType str = mapParseRun (parseTypeST str)

-- | Annotate a PLC program, so that all names are annotated with their types/kinds.
annotateProgram :: (MonadError (Error a) m, MonadQuote m) => Program TyName Name a -> m (Program TyNameWithKind NameWithType a)
annotateProgram (Program a v t) = Program a v <$> annotateTerm t

-- | Annotate a PLC term, so that all names are annotated with their types/kinds.
annotateTerm :: forall m a . (MonadError (Error a) m, MonadQuote m) => Term TyName Name a -> m (Term TyNameWithKind NameWithType a)
annotateTerm t = convertErrors asError $ do
    (ts, t') <- liftEither $ annotateTermST t
    updateMaxU ts
    pure t'
        where
            updateMaxU (TypeState _ tys) = do
                nextU <- liftQuote get
                let tsMaxU = maybe 0 (fst . fst) (IM.maxViewWithKey tys)
                let maxU = unUnique nextU - 1
                liftQuote $ put $ Unique $ max maxU tsMaxU

-- | Typecheck a PLC program.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m) => Natural -> Program TyNameWithKind NameWithType a -> m (Type TyNameWithKind ())
typecheckProgram n (Program _ _ t) = typecheckTerm n t

-- | Typecheck a PLC term.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m) => Natural -> Term TyNameWithKind NameWithType a -> m (Type TyNameWithKind ())
typecheckTerm n t = convertErrors asError $ do
    nextU <- liftQuote get
    let maxU = unUnique nextU - 1
    liftEither $ runTypeCheckM maxU n (typeOf t)
