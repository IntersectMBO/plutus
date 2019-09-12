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
        (AccountId 0 "alice") "alice"
        (Constant 450))
     (When [
           (Case
              (Choice
                 (ChoiceId "choice" "alice") [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "choice" "bob") [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "choice" "alice")
                             (Constant 42))
                          (ChoiceValue
                             (ChoiceId "choice" "bob")
                             (Constant 42)))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "choice" "alice")
                                (Constant 42))
                             (Constant 0))
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund) Refund)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "choice" "carol") [
                                   (Bound 1 1)]) Refund)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "choice" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Refund))] 100 Refund)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "choice" "carol") [
                             (Bound 1 1)]) Refund)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "choice" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund))] 100 Refund)))
           ,
           (Case
              (Choice
                 (ChoiceId "choice" "bob") [
                 (Bound 0 1)])
              (When [
                 (Case
                    (Choice
                       (ChoiceId "choice" "alice") [
                       (Bound 0 1)])
                    (If
                       (ValueEQ
                          (ChoiceValue
                             (ChoiceId "choice" "alice")
                             (Constant 42))
                          (ChoiceValue
                             (ChoiceId "choice" "bob")
                             (Constant 42)))
                       (If
                          (ValueEQ
                             (ChoiceValue
                                (ChoiceId "choice" "alice")
                                (Constant 42))
                             (Constant 0))
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund) Refund)
                       (When [
                             (Case
                                (Choice
                                   (ChoiceId "choice" "carol") [
                                   (Bound 1 1)]) Refund)
                             ,
                             (Case
                                (Choice
                                   (ChoiceId "choice" "carol") [
                                   (Bound 0 0)])
                                (Pay
                                   (AccountId 0 "alice")
                                   (Party "bob")
                                   (Constant 450) Refund))] 100 Refund)))] 60
                 (When [
                       (Case
                          (Choice
                             (ChoiceId "choice" "carol") [
                             (Bound 1 1)]) Refund)
                       ,
                       (Case
                          (Choice
                             (ChoiceId "choice" "carol") [
                             (Bound 0 0)])
                          (Pay
                             (AccountId 0 "alice")
                             (Party "bob")
                             (Constant 450) Refund))] 100 Refund)))] 40 Refund))] 10 Refund
|]

runHaskell :: ByteString -> IO (Either InterpreterError (InterpreterResult RunResult))
runHaskell = let maxInterpretationTime :: Microsecond = fromMicroseconds 10000000 in
                runExceptT . Interpreter.runHaskell maxInterpretationTime . SourceCode . Text.pack . BSC.unpack
