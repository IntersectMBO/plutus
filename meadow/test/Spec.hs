{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
module Main (main) where

import           API                   (MeadowError, RunResult (RunResult), SourceCode (SourceCode))
import           Control.Monad.Except  (runExceptT)
import           Data.ByteString       (ByteString)
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Text             as Text
import qualified Interpreter
import           Meadow.Contracts      (basicContract)
import           Test.Hspec            (Spec, describe, hspec, it, shouldBe)
import           Text.RawString.QQ     (r)

main :: IO ()
main = hspec runBasicSpec

runBasicSpec :: Spec
runBasicSpec = describe "Basic Contract" $
    it "should compile" $ runHaskell basicContract >>= (`shouldBe` basicResult)
    where
        basicResult = Right . RunResult $ [r|CommitCash (IdentCC 1) 1
           (ConstMoney 450)
           10 100
           (When (OrObs (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 0)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 0)
                                              (PersonChoseThis (IdentChoice 3) 3 0)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 0)
                                       (PersonChoseThis (IdentChoice 3) 3 0)))
                        (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                       (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                              (PersonChoseThis (IdentChoice 3) 3 1)))
                               (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                       (PersonChoseThis (IdentChoice 3) 3 1))))
                 90
                 (Choice (OrObs (AndObs (PersonChoseThis (IdentChoice 1) 1 1)
                                        (OrObs (PersonChoseThis (IdentChoice 2) 2 1)
                                               (PersonChoseThis (IdentChoice 3) 3 1)))
                                (AndObs (PersonChoseThis (IdentChoice 2) 2 1)
                                        (PersonChoseThis (IdentChoice 3) 3 1)))
                         (Pay (IdentPay 1) 1 2
                              (AvailableMoney (IdentCC 1))
                              100
                              (RedeemCC (IdentCC 1) Null))
                         (RedeemCC (IdentCC 1) Null))
                 (RedeemCC (IdentCC 1) Null))
           Null
|]

runHaskell :: ByteString -> IO (Either MeadowError RunResult)
runHaskell = runExceptT . Interpreter.runHaskell . SourceCode . Text.pack . BSC.unpack
