{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Crypto.Utils
  ( failWithMessage
  , byteStringAsHex
  , cryptoDisabled
  ) where

import PlutusCore.Builtin.Result
  ( BuiltinResult
  , builtinResultFailure
  , emit
  )

import Data.ByteString (ByteString, foldr')
import Data.Kind (Type)
import Data.Text (Text)
import Text.Printf (printf)

cryptoDisabled :: forall (a :: Type). String -> a
cryptoDisabled op =
  error $
    "This build of Plutus Core was compiled without cryptographic support \
    \(the with-crypto Cabal flag is disabled), so the builtin "
      <> op
      <> " cannot be evaluated. Rebuild with the with-crypto flag enabled to \
         \obtain an evaluator that links the C cryptography libraries."

failWithMessage :: forall (a :: Type). Text -> Text -> BuiltinResult a
failWithMessage location reason = do
  emit $ location <> ": " <> reason
  builtinResultFailure

byteStringAsHex :: ByteString -> String
byteStringAsHex bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w) : s) [] bs)
