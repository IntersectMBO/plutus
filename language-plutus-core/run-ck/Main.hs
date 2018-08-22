{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.CkMachine
import           PlutusPrelude

import           Control.Monad
import qualified Data.ByteString.Lazy          as BSL
import           Data.List
import qualified Data.Text                     as Text
import           Data.Text.Encoding            (encodeUtf8)
import qualified Data.Text.IO                  as Text

-- | Parse a program and run it using the CK machine.
parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

-- | Read-eval-print loop.
repl :: IO ()
repl = do
    line <- Text.getLine
    unless (line == ":q") $ do
        unless (Text.null line) $ do
            let res = parseRunCk . BSL.fromStrict $ encodeUtf8 line
            Text.putStrLn $ "Result: " <> either prettyText prettyText res <> "\n"
        repl

main :: IO ()
main = do
    putStrLn $ intercalate "\n"
        [ ""
        , "Type a program, press <enter> and the CK machine will run the program and print the result."
        , "You can type as many programs as you wish."
        , "Empty lines are ignored."
        , "Type \":q\" without the quotes to quit."
        , ""
        ]
    repl
