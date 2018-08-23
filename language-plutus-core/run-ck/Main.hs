{-# LANGUAGE OverloadedStrings #-}
module Main where

import           PlutusPrelude
import           Language.PlutusCore
import           Language.PlutusCore.CkMachine

import           Data.List
import           Control.Monad
import qualified Data.ByteString.Lazy as BSL
import           Data.Text (Text)
import qualified Data.Text    as Text
import qualified Data.Text.IO as Text
import           Data.Text.Encoding (encodeUtf8)

-- | Parse a program and run it using the CK machine.
parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

-- | Parse a program, run it and prettyprint the result.
textRunCk :: Text -> Text
textRunCk = either prettyText prettyText . parseRunCk . BSL.fromStrict . encodeUtf8

-- | Read-eval-print loop.
repl :: IO ()
repl = do
    line <- Text.getLine
    unless (line == ":q") $ do
        unless (Text.null line) $
            Text.putStrLn $ "Result: " <> textRunCk line <> "\n"
        repl

interactive :: IO ()
interactive = do
    putStrLn $ intercalate "\n"
        [ ""
        , "Type a program, press <enter> and the CK machine will run the program and print the result."
        , "You can type as many programs as you wish."
        , "Empty lines are ignored."
        , "Type \":q\" without the quotes to quit."
        , ""
        ]
    repl

nonInteractive :: IO ()
nonInteractive = Text.getLine >>= Text.putStrLn . textRunCk

main :: IO ()
main = nonInteractive
