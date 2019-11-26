{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Type.Instance.Pretty.Common
    ( prettyBytes
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Type.Core

import qualified Data.ByteString.Lazy               as BSL
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import           Numeric                            (showHex)

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

prettyBytes :: BSL.ByteString -> Doc ann
prettyBytes b = "#" <> fold (asBytes <$> BSL.unpack b)

instance Pretty BuiltinName where
    pretty AddInteger           = "addInteger"
    pretty SubtractInteger      = "subtractInteger"
    pretty MultiplyInteger      = "multiplyInteger"
    pretty DivideInteger        = "divideInteger"
    pretty QuotientInteger      = "quotientInteger"
    pretty ModInteger           = "modInteger"
    pretty RemainderInteger     = "remainderInteger"
    pretty LessThanInteger      = "lessThanInteger"
    pretty LessThanEqInteger    = "lessThanEqualsInteger"
    pretty GreaterThanInteger   = "greaterThanInteger"
    pretty GreaterThanEqInteger = "greaterThanEqualsInteger"
    pretty EqInteger            = "equalsInteger"
    pretty Concatenate          = "concatenate"
    pretty TakeByteString       = "takeByteString"
    pretty DropByteString       = "dropByteString"
    pretty EqByteString         = "equalsByteString"
    pretty LtByteString         = "lessThanByteString"
    pretty GtByteString         = "greaterThanByteString"
    pretty SHA2                 = "sha2_256"
    pretty SHA3                 = "sha3_256"
    pretty VerifySignature      = "verifySignature"

instance Pretty DynamicBuiltinName where
    pretty (DynamicBuiltinName n) = pretty n

instance Pretty StagedBuiltinName where
    pretty (StaticStagedBuiltinName  n) = pretty n
    pretty (DynamicStagedBuiltinName n) = pretty n

instance Pretty TypeBuiltin where
    pretty TyInteger    = "integer"
    pretty TyByteString = "bytestring"
    pretty TyString     = "string"

instance Pretty (Version ann) where
    pretty (Version _ i j k) = pretty i <> "." <> pretty j <> "." <> pretty k
