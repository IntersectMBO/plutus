{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.Parser.Internal where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parsable
import           Language.PlutusCore.Universe

import           Control.Monad.Except

import           Data.Proxy
import qualified Data.Text                      as T

--- The Parse monad ---

type Parse = ExceptT (ParseError AlexPosn) Alex

parseError :: Token AlexPosn -> Parse b
parseError = throwError . Unexpected

--- Static built-in functions ---

getStaticBuiltinName :: T.Text -> Maybe StaticBuiltinName
getStaticBuiltinName = \case
    "addInteger"               -> Just AddInteger
    "subtractInteger"          -> Just SubtractInteger
    "multiplyInteger"          -> Just MultiplyInteger
    "divideInteger"            -> Just DivideInteger
    "quotientInteger"          -> Just QuotientInteger
    "modInteger"               -> Just ModInteger
    "remainderInteger"         -> Just RemainderInteger
    "lessThanInteger"          -> Just LessThanInteger
    "lessThanEqualsInteger"    -> Just LessThanEqInteger
    "greaterThanInteger"       -> Just GreaterThanInteger
    "greaterThanEqualsInteger" -> Just GreaterThanEqInteger
    "equalsInteger"            -> Just EqInteger
    "concatenate"              -> Just Concatenate
    "takeByteString"           -> Just TakeByteString
    "dropByteString"           -> Just DropByteString
    "equalsByteString"         -> Just EqByteString
    "lessThanByteString"       -> Just LtByteString
    "greaterThanByteString"    -> Just GtByteString
    "sha2_256"                 -> Just SHA2
    "sha3_256"                 -> Just SHA3
    "verifySignature"          -> Just VerifySignature
    "ifThenElse"               -> Just IfThenElse
    _                          -> Nothing


--- Parsing built-in types and constants ---

-- | Tags of types in the default universe.
encodeTyName :: T.Text -> Maybe [Int]
encodeTyName = \case
    "bool"       -> Just $ encodeUni DefaultUniBool
    "bytestring" -> Just $ encodeUni DefaultUniByteString
    "char"       -> Just $ encodeUni DefaultUniChar
    "integer"    -> Just $ encodeUni DefaultUniInteger
    "string"     -> Just $ encodeUni DefaultUniString
    "unit"       -> Just $ encodeUni DefaultUniUnit
    _ -> Nothing

-- | Given a type name, return a type in the (default) universe.
-- This can fail in two ways: there's no type with that name, or decodeUni fails because
-- it's been given an unknown tag.  In both cases we report an unknown built-in type.
decodeTyName :: Closed uni => AlexPosn -> T.Text -> Parse (Some (TypeIn uni))
decodeTyName tyloc tyname =
    case encodeTyName tyname >>= decodeUni of
        Nothing -> throwError $ UnknownBuiltinType tyloc tyname
        Just ty -> pure ty

-- | Convert a textual type name into a Type.
mkBuiltinType :: Closed uni => AlexPosn -> T.Text -> Parse (Type TyName uni AlexPosn)
mkBuiltinType tyloc tyname = TyBuiltin tyloc <$> decodeTyName tyloc tyname

-- | Produce (the contents of) a constant term from a type name and a literal constant.
-- We return a pair of the position and the value rather than the actual term, since we want
-- to share this between UPLC and TPLC.
mkBuiltinConstant
  :: (Closed uni, uni `Everywhere` Parsable)
  => AlexPosn -> T.Text -> AlexPosn -> T.Text -> Parse (AlexPosn, Some (ValueOf uni))
mkBuiltinConstant tyloc tyname litloc lit  = do
    Some (TypeIn uni1) <- decodeTyName tyloc tyname
    case bring (Proxy @Parsable) uni1 (parseConstant lit) of
        Nothing -> throwError $ InvalidBuiltinConstant litloc lit tyname
        Just w  -> pure (litloc, Some (ValueOf uni1 w))

-- | Produce (the contents of) a builtin function term from a type name and a literal constant.
-- We return a pair of the position and the value rather than the actual term, since we want
-- to share this between UPLC and TPLC.
mkBuiltinFunction :: a -> T.Text -> (a, BuiltinName)
mkBuiltinFunction loc ident =
    case getStaticBuiltinName ident of
        Just b  -> (loc, StaticBuiltinName b)
        Nothing -> (loc, (DynBuiltinName (DynamicBuiltinName ident)))
