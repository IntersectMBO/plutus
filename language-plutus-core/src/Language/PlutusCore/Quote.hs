{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.PlutusCore.Quote (
              runQT
            , runQ
            , freshName
            , freshTyName
            , parse
            , QT
            , Q
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

-- | The "quotation" monad transformer. This allows creation of fresh names and parsing.
newtype QT m a = QT { unQT :: StateT IdentifierState m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadState IdentifierState)

-- | Run a quote from an empty identifier state.
runQT ::  (Monad m) => QT m a -> m a
runQT q = evalStateT (unQT q) emptyIdentifierState

type Q a = QT Identity a

-- | Run a quote from an empty identifier state.
runQ :: Q a -> a
runQ = runIdentity . runQT

freshName :: (Monad m) => a -> BSL.ByteString -> QT m (Name a)
freshName ann str = do
  s1 <- get
  let (u, s2) = newIdentifier str s1
  put s2
  pure $ Name ann str u

freshTyName :: (Monad m) => a -> BSL.ByteString -> QT m (TyName a)
freshTyName = fmap TyName .* freshName

parse :: (MonadError ParseError m) => BSL.ByteString -> QT m (Program TyName Name AlexPosn)
parse str = QT $ mapStateT (liftEither . runExcept) (parseST str)
