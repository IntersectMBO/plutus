{-# LANGUAGE TypeApplications #-}
module Spec.State where

import           Control.Applicative
import           Control.Monad                         (foldM)
import           Control.Monad.Except                  (runExcept)
import           Control.Monad.Writer                  (runWriterT)
import qualified Data.Aeson                            as Aeson
import           Data.Either                           (fromRight, isRight)
import           Language.Plutus.Contract              as Con
import qualified Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Record
import           Test.Tasty
import qualified Test.Tasty.HUnit                      as HUnit

import qualified Language.Plutus.Contract.Resumable    as S

tests :: TestTree
tests =
    let ep = Con.endpoint @String "endpoint"
        initRecord = fmap fst . fst . fromRight (error "initialise failed") . runExcept . runWriterT . S.initialise
        inp = Event.endpoint "endpoint" (Aeson.toJSON "asd")
        run con =
            let con' = Con.convertContract con in
            foldM (fmap (fmap fst) . S.insertAndUpdate con') (initRecord con')
    in
    testGroup "stateful contract"
        [ HUnit.testCase "run a contract without checkpoints" $
            let res = run ep [inp]
            in HUnit.assertBool "init" (isRight res)

        , HUnit.testCase "run a contract with checkpoints, recording the result as JSON" $
            let con = S.checkpoint $ (,) <$> S.checkpoint ep <*> (ep >> ep)
                res = run con [inp, inp]
            in HUnit.assertBool "checkpoint" (res == Right (Right (jsonLeaf ("asd", "asd"))))

        , HUnit.testCase "run a parallel contract with checkpoints, recording the result as JSON" $
        let con = S.checkpoint $ (ep >> ep) <|> (ep >> ep >> ep)
            res = run con [inp, inp]
        in HUnit.assertBool "checkpoint" (res == Right (Right (jsonLeaf "asd")))

        ]
