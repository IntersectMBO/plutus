{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import           API                          (RunResult (RunResult))
import           Control.Monad.Except         (runExceptT)
import           Data.ByteString              (ByteString)
import qualified Data.ByteString.Char8        as BSC
import qualified Data.Text                    as Text
import           Data.Time.Units              (Second)
import qualified Interpreter
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult (InterpreterResult),
                                               SourceCode (SourceCode))
import           Marlowe.Contracts            (escrow)
import           Test.Hspec                   (Spec, describe, hspec, it, shouldBe)
import           Text.RawString.QQ            (r)

main :: IO ()
main = hspec runBasicSpec

runBasicSpec :: Spec
runBasicSpec = describe "Basic Contract" $
    it "should compile" $ runHaskell escrow >>= (`shouldBe` escrowResult)
    where
        escrowResult = Right . InterpreterResult [] . RunResult $ [r|When [
  (Case
     (Deposit
        (AccountId 0
           (Role "alice"))
        (Role "alice")
        (Token "" "")
        (Constant 450))
     (When [
           (Case
              (Choice
                 (ChoiceId "choice"
                    (Role "alice")) [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "choice"
                          (Role "bob")) [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "choice"
                                (Role "alice")))
                          (ChoiceValue
                             (ChoiceId "choice"
                                (Role "bob"))))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "choice"
                                   (Role "alice")))
                             (Constant 0))
                          (Pay
                             (AccountId 0
                                (Role "alice"))
                             (Party
                                (Role "bob"))
                             (Token "" "")
                             (Constant 450) Close) Close)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "choice"
                                      (Role "carol")) [
                                   (Bound 1 1)]) Close)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "choice"
                                      (Role "carol")) [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0
                                      (Role "alice"))
                                   (Party
                                      (Role "bob"))
                                   (Token "" "")
                                   (Constant 450) Close))] 100 Close)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "choice"
                                (Role "carol")) [
                             (Bound 1 1)]) Close)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "choice"
                                (Role "carol")) [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0
                                (Role "alice"))
                             (Party
                                (Role "bob"))
                             (Token "" "")
                             (Constant 450) Close))] 100 Close)))
           ,
           (Case
              (Choice
                 (ChoiceId "choice"
                    (Role "bob")) [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "choice"
                          (Role "alice")) [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "choice"
                                (Role "alice")))
                          (ChoiceValue
                             (ChoiceId "choice"
                                (Role "bob"))))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "choice"
                                   (Role "alice")))
                             (Constant 0))
                          (Pay
                             (AccountId 0
                                (Role "alice"))
                             (Party
                                (Role "bob"))
                             (Token "" "")
                             (Constant 450) Close) Close)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "choice"
                                      (Role "carol")) [
                                   (Bound 1 1)]) Close)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "choice"
                                      (Role "carol")) [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0
                                      (Role "alice"))
                                   (Party
                                      (Role "bob"))
                                   (Token "" "")
                                   (Constant 450) Close))] 100 Close)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "choice"
                                (Role "carol")) [
                             (Bound 1 1)]) Close)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "choice"
                                (Role "carol")) [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0
                                (Role "alice"))
                             (Party
                                (Role "bob"))
                             (Token "" "")
                             (Constant 450) Close))] 100 Close)))] 40 Close))] 10 Close
|]

runHaskell :: ByteString -> IO (Either InterpreterError (InterpreterResult RunResult))
runHaskell =
    let maxInterpretationTime = (15 :: Second)
     in runExceptT .
        Interpreter.runHaskell maxInterpretationTime .
        SourceCode . Text.pack . BSC.unpack
