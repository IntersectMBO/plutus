{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Crypto.Utils (failWithMessage, byteStringAsHex) where

import PlutusCore.Builtin.Emitter (emit)
import PlutusCore.Builtin.Result (BuiltinResult)
import PlutusCore.Evaluation.Result (evaluationFailure)

import Data.ByteString (ByteString, foldr')
import Data.Kind (Type)
import Data.Text (Text)
import Text.Printf (printf)

failWithMessage :: forall (a :: Type). Text -> Text -> BuiltinResult a
failWithMessage location reason = do
  emit $ location <> ": " <> reason
  evaluationFailure

byteStringAsHex :: ByteString -> String
byteStringAsHex bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w):s) [] bs)
