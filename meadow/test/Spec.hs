{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import           API                          (RunResult (RunResult))
import           Control.Monad.Except         (runExceptT)
import           Data.ByteString              (ByteString)
import qualified Data.ByteString.Char8        as BSC
import qualified Data.Text                    as Text
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import qualified Interpreter
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult (InterpreterResult),
                                               SourceCode (SourceCode))
import           Meadow.Contracts             (escrow)
import           Test.Hspec                   (Spec, describe, hspec, it, shouldBe)
import           Text.RawString.QQ            (r)

main :: IO ()
main = hspec runBasicSpec

runBasicSpec :: Spec
runBasicSpec = describe "Basic Contract" $
    it "should compile" $ runHaskell escrow >>= (`shouldBe` escrowResult)
    where
        escrowResult = Right . InterpreterResult [] . RunResult $ [r|Commit 1 1 1
  (Constant 450) 10 100
  (When
     (OrObs
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 0)
              (OrObs
                 (ChoseThis (1, 2) 0)
                 (ChoseThis (1, 3) 0)))
           (AndObs
              (ChoseThis (1, 2) 0)
              (ChoseThis (1, 3) 0)))
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 1)
              (OrObs
                 (ChoseThis (1, 2) 1)
                 (ChoseThis (1, 3) 1)))
           (AndObs
              (ChoseThis (1, 2) 1)
              (ChoseThis (1, 3) 1)))) 90
     (Choice
        (OrObs
           (AndObs
              (ChoseThis (1, 1) 1)
              (OrObs
                 (ChoseThis (1, 2) 1)
                 (ChoseThis (1, 3) 1)))
           (AndObs
              (ChoseThis (1, 2) 1)
              (ChoseThis (1, 3) 1)))
        (Pay 2 1 2
           (Committed 1) 100 Null Null)
        (Pay 3 1 1
           (Committed 1) 100 Null Null))
     (Pay 4 1 1
        (Committed 1) 100 Null Null)) Null
|]

runHaskell :: ByteString -> IO (Either InterpreterError (InterpreterResult RunResult))
runHaskell = let maxInterpretationTime :: Microsecond = fromMicroseconds 5000000 in
                runExceptT . Interpreter.runHaskell maxInterpretationTime . SourceCode . Text.pack . BSC.unpack
