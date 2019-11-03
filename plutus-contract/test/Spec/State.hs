{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Spec.State where

import           Control.Applicative                             (Alternative (..))
import           Control.Lens                                    (from, view)
import           Control.Monad                                   (foldM)
import           Control.Monad.Except                            (runExcept)
import           Control.Monad.Writer                            (runWriterT)
import           Data.Either                                     (fromRight, isRight)
import           Language.Plutus.Contract                        as Con
import           Language.Plutus.Contract.Record                 (Record (ClosedRec), jsonLeaf, record)
import           Test.Tasty
import qualified Test.Tasty.HUnit                                as HUnit

import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoint
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
        initRecord = view (from record) . fmap fst . fst . fromRight (error "initialise failed") . runExcept . runWriterT . S.initialise
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
            in HUnit.assertBool "checkpoint" (res == Right (ClosedRec (jsonLeaf ("asd", "asd"))))

        , HUnit.testCase "run a parallel contract with checkpoints, recording the result as JSON" $
        let con = S.checkpoint $ (ep >> ep) <|> (ep >> ep >> ep)
            res = run con [inp, inp]
        in HUnit.assertBool "checkpoint" (res == Right (ClosedRec (jsonLeaf "asd")))

        , HUnit.testCase "run a parallel contract in which the right branch finished first" $
        let con = S.checkpoint $ do
                    (l, r) <- both ep ((ep >> ep >> ep) <|> (ep >> ep))
                    _ <- ep
                    pure (l <> r)
            res = run con [inp, inp, inp, inp]
        in HUnit.assertBool "checkpoint" (res == Right (ClosedRec (jsonLeaf "asdasd")))

        ]
