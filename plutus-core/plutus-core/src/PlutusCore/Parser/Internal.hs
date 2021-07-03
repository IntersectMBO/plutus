{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Parser.Internal where

import           PlutusPrelude

import           PlutusCore.Core
import           PlutusCore.Error
import           PlutusCore.Lexer
import           PlutusCore.Lexer.Type
import           PlutusCore.Name
import           PlutusCore.Parsable

import           Control.Monad.Except
import           Universe

import           Data.List             (find)
import           Data.Proxy
import qualified Data.Text             as T

--- The Parse monad ---

type Parse = ExceptT (ParseError AlexPosn) Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwError . Unexpected

--- Parsing built-in functions ---

parseBuiltinFunction :: (Bounded fun, Enum fun, Pretty fun) => T.Text -> Maybe fun
parseBuiltinFunction name = find (\fun -> display fun == name) enumeration

--- Parsing built-in types and constants ---

-- | Given a type name, return a type in the (default) universe.
-- This can fail in two ways: there's no type with that name, or decodeUni fails because
-- it's been given an unknown tag.  In both cases we report an unknown built-in type.
decodeTypeName
    :: Parsable (SomeTypeIn (Kinded uni))
    => AlexPosn -> T.Text -> Parse (SomeTypeIn (Kinded uni))
decodeTypeName tyloc typeName =
    case parse typeName of
        Nothing -> throwError $ UnknownBuiltinType tyloc typeName
        Just ty -> pure ty

-- | Convert a textual type name into a Type.
mkBuiltinType
    :: Parsable (SomeTypeIn (Kinded uni))
    => AlexPosn -> T.Text -> Parse (Type TyName uni AlexPosn)
mkBuiltinType tyloc typeName =
    decodeTypeName tyloc typeName <&> \(SomeTypeIn (Kinded uni)) ->
        TyBuiltin tyloc $ SomeTypeIn uni

-- | Produce (the contents of) a constant term from a type name and a literal constant.
-- We return a pair of the position and the value rather than the actual term, since we want
-- to share this between UPLC and TPLC.
mkBuiltinConstant
    :: forall uni. (Parsable (SomeTypeIn (Kinded uni)), Closed uni, uni `Everywhere` Parsable)
    => AlexPosn -> T.Text -> AlexPosn -> T.Text -> Parse (AlexPosn, Some (ValueOf uni))
mkBuiltinConstant tyloc typeName litloc lit = do
    SomeTypeIn (Kinded uni) <- decodeTypeName tyloc typeName
    -- See Note [Decoding universes].
    case checkStar @uni uni of
        Nothing -> throwError undefined
        Just Refl -> case bring (Proxy @Parsable) uni (parse lit) of
            Nothing -> throwError $ InvalidBuiltinConstant litloc lit typeName
            Just w  -> pure (litloc, Some (ValueOf uni w))

-- | Produce (the contents of) a builtin function term from a type name and a literal constant.
-- We return a pair of the position and the value rather than the actual term, since we want
-- to share this between UPLC and TPLC.
mkBuiltinFunction
    :: (Bounded fun, Enum fun, Pretty fun)
    => AlexPosn -> T.Text -> Parse (AlexPosn, fun)
mkBuiltinFunction loc ident =
    case parseBuiltinFunction ident of
        Just b  -> pure (loc, b)
        Nothing -> throwError $ UnknownBuiltinFunction loc ident
