{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Spec.State where

import           Control.Monad.Freer                (Eff, run)
import           Control.Monad.Freer.Extras         (raiseEnd)
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Data.Foldable                      (foldl')
import qualified Data.Map                           as Map
import           Data.Maybe                         (isJust)
import           Test.Tasty
import qualified Test.Tasty.HUnit                   as HUnit

import           Language.Plutus.Contract.Resumable (IterationID (..), MultiRequestContStatus, Request (..),
                                                     RequestID (..), Requests (..), Response (..), Responses (..),
                                                     Resumable, prompt, select)
import qualified Language.Plutus.Contract.Resumable as S
import           Language.Plutus.Contract.Util      (loopM)

runResumableTest ::
    forall i o a.
    Responses i
    -> Eff '[Resumable i o] a
    -> (Maybe a, Requests o)
runResumableTest events action =
    let r = run . evalState (mempty @(Responses i))
        initial = r $ S.suspendNonDet @i @o @a $ S.handleResumable $ raiseEnd action
        mkResp (itId, rqId) evt = Response{rspRqID = rqId, rspItID = itId, rspResponse=evt}
        go :: Maybe (MultiRequestContStatus i o '[State (Responses i)] a) -> Response i -> Maybe (MultiRequestContStatus i o '[State (Responses i)] a)
        go (Just (S.AContinuation S.MultiRequestContinuation{S.ndcRequests, S.ndcCont})) rsp = r (ndcCont rsp)
        go _ _                                                                               = Nothing
        result = foldl' go initial (S.responses events)
    in case result of
        Nothing                                                          -> (Nothing, mempty)
        Just (S.AResult a)                                               -> (Just a, mempty)
        Just (S.AContinuation S.MultiRequestContinuation{S.ndcRequests}) -> (Nothing, ndcRequests)

tests :: TestTree
tests = testGroup "stateful contract"
    [ HUnit.testCase "run a contract without prompts" $
        let res = runResumableTest @Int @String mempty (pure ())
        in HUnit.assertBool "run a contract without prompts" (isJust $ fst res)

    , HUnit.testCase "run a contract with a single prompt" $
        let (_, Requests{unRequests}) = runResumableTest @Int @String mempty (askStr "prompt1")
        in HUnit.assertEqual
            "run a contract with a single prompt"
            unRequests
            [Request{rqID = RequestID 1, itID = IterationID 1, rqRequest = "prompt1"}]

    , HUnit.testCase "run a contract with two prompts" $
        let (_, Requests{unRequests}) = runResumableTest @Int @String mempty (askStr "prompt1" `selectStr` askStr "prompt2")
        in HUnit.assertEqual
            "run a contract with two prompts"
            [ Request{rqID = RequestID 2, itID = IterationID 1, rqRequest = "prompt2"}
            , Request{rqID = RequestID 1, itID = IterationID 1, rqRequest = "prompt1"}
            ]
            unRequests

    , HUnit.testCase "run a contract with a two prompts and one answer" $
        let record = Responses $ Map.singleton (1, 2) 5
            (result, _) = runResumableTest @Int @String record ((askStr "prompt1" >> pure "branch 1") `selectStr` (askStr "prompt2" >> pure "branch 2"))
        in HUnit.assertEqual "run a contract with a two prompts and one answer" (Just "branch 2") result

    , HUnit.testCase "commit to a branch" $
        let record = Responses $ Map.singleton (1, 1) 5
            (_, Requests{unRequests}) = runResumableTest @Int @String record ((askStr "prompt1" >> askStr "prompt3") `selectStr` (askStr "prompt2" >> pure 10))
        in HUnit.assertEqual
                "commit to a branch"
                [ Request{rqID = RequestID 1, itID = IterationID 2, rqRequest = "prompt3"} ]
                unRequests

    , HUnit.testCase "commit to a branch (II)" $
        let record = Responses $ Map.singleton (1, 2) 5
            (_, Requests{unRequests}) = runResumableTest @Int @String record ((askStr "prompt2" >> pure 10) `selectStr` (askStr "prompt1" >> askStr "prompt3"))
        in HUnit.assertEqual
            "commit to a branch (II)"
            [ Request{rqID = RequestID 1, itID = IterationID 2, rqRequest = "prompt3"} ]
            unRequests

    , HUnit.testCase "return a result" $
        let record = Responses $ Map.singleton (1, 2) 5
            (result, _) = runResumableTest @Int @String record ((askStr "prompt1" >> askStr "prompt4") `selectStr` (askStr "prompt2" >> pure 10) `selectStr` (askStr "prompt3" >> askStr "prompt5"))
        in HUnit.assertEqual "return a result" (Just 10) result

    , HUnit.testCase "go into a branch" $
        let record = Responses $ Map.fromList [((IterationID 1, RequestID 2), 5), ((IterationID 2, RequestID 2), 10) ]
            (result, _) = runResumableTest @Int @String record
                ((askStr "prompt1" >> askStr "prompt4")
                `selectStr`
                    (askStr "prompt2" >> (askStr "prompt5" `selectStr` (askStr "prompt6" >> pure 11) `selectStr` askStr "prompt8"))
                    `selectStr` (askStr "prompt3" >> askStr "prompt7"))
        in HUnit.assertEqual "go into a branch" (Just 11) result

    , HUnit.testCase "loop" $
        let record = Responses
                 $ Map.fromList
                    [ ((IterationID 1, RequestID 1), 1)
                    , ((IterationID 2, RequestID 1), 1)
                    , ((IterationID 3, RequestID 1), 1)
                    , ((IterationID 4, RequestID 2), 1)
                    ]
            stopLeft = askStr "stop left" >> pure (10 :: Int)
            stopRight = askStr "stop right" >> pure 11
            (result, _) = runResumableTest @Int @String record $
                loopM (const $ (Left <$> askStr "keep going") `selectStr` (Right <$> (stopLeft `selectStr` stopRight))) 0
        in HUnit.assertEqual "loop" (Just 10) result

    , HUnit.testCase "loop requests" $
        let record = Responses
                 $ Map.fromList
                    [ ((IterationID 1, RequestID 1), 1)
                    , ((IterationID 2, RequestID 1), 1)
                    , ((IterationID 3, RequestID 1), 1)
                    ]
            stopLeft = askStr "stop left" >> pure (10 :: Int)
            stopRight = askStr "stop right" >> pure 11
            (_, Requests{unRequests}) = runResumableTest @Int @String record $
                loopM (const $ (Left <$> askStr "keep going") `selectStr` (Right <$> (stopLeft `selectStr` stopRight))) 0
        in HUnit.assertEqual "loop requests"
            [ Request{rqID = RequestID 3, itID = IterationID 4, rqRequest = "stop right"}
            , Request{rqID = RequestID 2, itID = IterationID 4, rqRequest = "stop left"}
            , Request{rqID = RequestID 1, itID = IterationID 4, rqRequest = "keep going"}
            ]
            unRequests

    ]

askStr :: String -> Eff '[Resumable Int String] Int
askStr = prompt

selectStr :: Eff '[Resumable Int String] a -> Eff '[Resumable Int String] a -> Eff '[Resumable Int String] a
selectStr = select @Int @String @'[Resumable Int String]
