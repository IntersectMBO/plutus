{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module PlutusCore.Parser
    ( parseProgram
    , parseTerm
    , parseType
    , ParseError(..)
    , IdentifierState
    , emptyIdentifierState
    ) where

import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Mark
import PlutusCore.MkPlc (mkConstant, mkTyBuiltin)
import PlutusCore.Name
import PlutusCore.Parsable
import PlutusCore.Parser.Type
import PlutusCore.Quote
import PlutusPrelude
import Universe

import Control.Monad.Except
import Control.Monad.State
import Data.ByteString.Lazy (ByteString)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified
import Data.Proxy
import Data.Text qualified as T
import Text.Megaparsec (SourcePos)

tyInst :: a -> Term tyname name uni fun a -> NonEmpty (Type tyname uni a) -> Term tyname name uni fun a
tyInst loc t (ty :| [])  = TyInst loc t ty
tyInst loc t (ty :| tys) = TyInst loc (tyInst loc t (ty:|init tys)) (last tys)

tyApps :: a -> Type tyname uni a -> NonEmpty (Type tyname uni a) -> Type tyname uni a
tyApps loc ty (ty' :| [])  = TyApp loc ty ty'
tyApps loc ty (ty' :| tys) = TyApp loc (tyApps loc ty (ty':|init tys)) (last tys)

app :: a -> Term tyname name uni fun a -> NonEmpty (Term tyname name uni fun a) -> Term tyname name uni fun a
app loc t (t' :| []) = Apply loc t t'
app loc t (t' :| ts) = Apply loc (app loc t (t':|init ts)) (last ts)

--- Running the parser ---

-- parseST :: Parse a -> ByteString -> StateT IdentifierState (Except ParseError) a
-- parseST p str = runAlexST' str (runExceptT p) >>= liftEither

mapParseRun :: (AsParseError e, MonadError e m, MonadQuote m) => StateT IdentifierState (Except ParseError) b -> m b
-- we need to run the parser starting from our current next unique, then throw away the rest of the
-- parser state and get back the new next unique
mapParseRun run = do
    nextU <- liftQuote freshUnique
    (p, (_, u)) <- throwingEither _ParseError $ runExcept $ runStateT run (identifierStateFrom nextU)
    liftQuote $ markNonFreshBelow u
    pure p

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (MonadError e m, MonadQuote m) => ByteString -> m (Program TyName Name DefaultUni DefaultFun SourcePos)
parseProgram str = undefined
-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (MonadError e m, MonadQuote m) => ByteString -> m (Term TyName Name DefaultUni DefaultFun SourcePos)
parseTerm str = undefined

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: ByteString -> m (Type TyName DefaultUni SourcePos)
parseType str = undefined
