{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Spec.State where

import           Data.Either                                     (isRight)
import           Language.Plutus.Contract                        as Con
import           Language.Plutus.Contract.Record                 (Record (ClosedRec), jsonLeaf)
import           Test.Tasty
import qualified Test.Tasty.HUnit                                as HUnit

import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import           Language.Plutus.Contract.Resumable              (ResumableResult (..))
import qualified Language.Plutus.Contract.Resumable              as S

type Schema =
    BlockchainActions
        .\/ Endpoint "endpoint" String

tests :: TestTree
tests =
    let
        epCon :: Con.Contract Schema () String
        epCon = Con.endpoint @"endpoint" @String @Schema
        ep = Con.unContract epCon
        inp = Endpoint.event @"endpoint" "asd"
    in
    testGroup "stateful contract"
        [ HUnit.testCase "run a contract without checkpoints" $
            let res = S.runResumable [inp] ep
            in HUnit.assertBool "init" (isRight res)

        , HUnit.testCase "run a contract with checkpoints, recording the result as JSON" $
            let con = S.checkpoint $ (,) <$> S.checkpoint ep <*> (ep >> ep)
                res = fmap wcsRecord $ S.runResumable [inp, inp, inp] con
            in HUnit.assertBool "checkpoint" (res == Right (ClosedRec (jsonLeaf ("asd", "asd"))))

        , HUnit.testCase "run a parallel contract with checkpoints, recording the result as JSON" $
        let con = S.checkpoint $ (ep >> ep) <|> (ep >> ep >> ep)
            res = fmap wcsRecord $ S.runResumable [inp, inp] con
        in HUnit.assertBool "checkpoint" (res == Right (ClosedRec (jsonLeaf "asd")))

        ]
