{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Type
import           Data.Text (Text)
import qualified Data.Text as Text

viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- TODO: this is a stub.
applyBuiltinSizeIntInt
  :: (Integer -> Integer -> Integer) -> [Constant ()] -> Either Text (Maybe (Constant ()))
applyBuiltinSizeIntInt op [BuiltinSize _ s, BuiltinInt _ n i, BuiltinInt _ m j] =
  Right . Just . BuiltinInt () m $ op i j

applyBuiltinName :: BuiltinName -> [Constant ()] -> Either Text (Maybe (Constant ()))
applyBuiltinName AddInteger           = applyBuiltinSizeIntInt (+)
applyBuiltinName SubtractInteger      = undefined
applyBuiltinName MultiplyInteger      = undefined
applyBuiltinName DivideInteger        = undefined
applyBuiltinName RemainderInteger     = undefined
applyBuiltinName LessThanInteger      = undefined
applyBuiltinName LessThanEqInteger    = undefined
applyBuiltinName GreaterThanInteger   = undefined
applyBuiltinName GreaterThanEqInteger = undefined
applyBuiltinName EqInteger            = undefined
applyBuiltinName IntToByteString      = undefined
applyBuiltinName Concatenate          = undefined
applyBuiltinName TakeByteString       = undefined
applyBuiltinName DropByteString       = undefined
applyBuiltinName ResizeByteString     = undefined
applyBuiltinName SHA2                 = undefined
applyBuiltinName SHA3                 = undefined
applyBuiltinName VerifySignature      = undefined
applyBuiltinName EqByteString         = undefined
applyBuiltinName TxHash               = undefined
applyBuiltinName BlockNum             = undefined
applyBuiltinName BlockTime            = undefined

applyConstant :: Constant () -> [Constant ()] -> Either Text (Maybe (Constant ()))
applyConstant (BuiltinName _ fun) args = applyBuiltinName fun args
applyConstant  constant           args = Left $ mconcat
  [ "Cannot reduce ("
  , Text.intercalate " " . map prettyText $ constant : args
  , ") because ("
  , prettyText constant
  , ") is not a function"
  ]
