{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.CkMachine

import           Control.Monad
import qualified Data.ByteString.Lazy          as BSL
import           Data.Text                     (Text)
import           Data.Text.Encoding            (encodeUtf8)
import qualified Data.Text.IO                  as Text

-- | Parse a program and run it using the CK machine.
parseRunCk :: BSL.ByteString -> Either (ParseError AlexPosn) CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

-- | Parse a program, run it and prettyprint the result.
textRunCk :: Text -> Text
textRunCk = either prettyCfgText prettyCfgText . parseRunCk . BSL.fromStrict . encodeUtf8

nonInteractive :: IO ()
nonInteractive = Text.getLine >>= Text.putStrLn . textRunCk

main :: IO ()
main = nonInteractive
