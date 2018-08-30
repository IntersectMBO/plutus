module Main (main) where

import           Language.PlutusCore
<<<<<<< HEAD
import           Language.PlutusCore.CkMachine
import           PlutusPrelude

import           Control.Monad
import qualified Data.ByteString.Lazy          as BSL
import           Data.List
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Data.Text.Encoding            (encodeUtf8)
import qualified Data.Text.IO                  as Text
=======

import           Control.Monad
import qualified Data.ByteString.Lazy as BSL
import           Data.Text            (Text)
import           Data.Text.Encoding   (encodeUtf8)
import qualified Data.Text.IO         as Text
>>>>>>> 3e0bd6917753c5373678c92796bed5257eeaa7f6

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
