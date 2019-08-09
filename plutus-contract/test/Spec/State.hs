{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Spec.State where

import           Control.Applicative                             (Alternative (..))
import           Control.Monad                                   (foldM)
import           Control.Monad.Except                            (runExcept)
import           Control.Monad.Writer                            (runWriterT)
import           Data.Either                                     (fromRight, isRight)
import           Language.Plutus.Contract                        as Con
import           Language.Plutus.Contract.Record                 (jsonLeaf)
import           Test.Tasty
import qualified Test.Tasty.HUnit                                as HUnit

import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import qualified Language.Plutus.Contract.Resumable              as S

type Schema =
    BlockchainActions
        .\/ Endpoint "endpoint" String

tests :: TestTree
tests =
    let ep = Con.endpoint @"endpoint" @String @Schema
        initRecord = fmap fst . fst . fromRight (error "initialise failed") . runExcept . runWriterT . S.initialise
        inp = Endpoint.event @"endpoint" "asd"
        run con =
            foldM (fmap (fmap fst) . S.insertAndUpdate con) (initRecord con)
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
