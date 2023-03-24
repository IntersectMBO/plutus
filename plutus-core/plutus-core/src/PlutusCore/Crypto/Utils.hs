{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Crypto.Utils (failWithMessage, byteStringAsHex)
where

import Data.ByteString (ByteString, foldr')
import Data.Kind (Type)
import Data.Text (Text)
import Text.Printf (printf)

import PlutusCore.Builtin.Emitter (Emitter, emit)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))

-- TODO: Something like 'failWithMessage x y *> foo' should really fail with
-- 'EvaluationFailure' without evaluating 'foo', but currently it will. This
-- requires a fix to how Emitter and EvaluationResult work, and since we don't
-- expect 'failWithMessage' to be used this way, we note this for future
-- reference only for when such fixes are made.
failWithMessage :: forall (a :: Type) .
  Text -> Text -> Emitter (EvaluationResult a)
failWithMessage location reason = do
  emit $ location <> ": " <> reason
  pure EvaluationFailure

byteStringAsHex :: ByteString -> String
byteStringAsHex bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w):s) [] bs)
