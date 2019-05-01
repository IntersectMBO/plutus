module Marlowe.ContractTests where

import Prelude

import Data.Either (Either(..))
import Data.Integral (fromIntegral)
import Data.Lens (set)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.List as List
import Data.Map as Map
import Data.Monoid (mempty)
import Data.Newtype (wrap)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Marlowe.Contracts as Contracts
import Marlowe.Parser (contract)
import Marlowe.Semantics (AnyInput(..), CommitInfo(..), CommitInfoRecord(..), Input(..), State(..))
import Marlowe.Test (Action(..), TestState, _state, initialState, run)
import Marlowe.Types (IdAction(..), IdChoice(..), IdCommit(..), Person(..), WIdChoice(..))
import Test.Unit (TestSuite, Test, failure, suite, test)
import Test.Unit.Assert (assert)
import Text.Parsing.Simple (parse)

all :: forall eff. TestSuite eff
all = suite "Contract Tests" do
        test "Escrow" do
          case parse contract Contracts.escrow of
            Left parseError -> failure "could not parse escrow contract"
            Right escrow -> let choiceA = IdChoice {choice: (fromIntegral 1), person: Person (fromIntegral 1)} 
                                choiceB = IdChoice {choice: (fromIntegral 1), person: Person (fromIntegral 2)}
                                actions = [ ApplyTransaction (Tuple 
                                                (List.fromFoldable [ Input (IChoice choiceA (fromIntegral 1))
                                                                   , Input (IChoice choiceB (fromIntegral 1))
                                                                   , Action (IdAction (fromIntegral 1))
                                                                   , Action (IdAction (fromIntegral 2))
                                                                   ]) 
                                                (Set.fromFoldable [Person (fromIntegral 1), Person (fromIntegral 2)]))
                                           ]
                                finalState = run escrow actions 
                                expectedState = State { choices: Map.fromFoldable [ Tuple (WIdChoice choiceA) (fromIntegral 1)
                                                                                  , Tuple (WIdChoice choiceB) (fromIntegral 1)
                                                                                  ]
                                                      , commits: CommitInfo { currentCommitsById: Map.fromFoldable [Tuple (wrap (fromIntegral 1)) (CommitInfoRecord { amount: (fromIntegral 0)
                                                                                                                                                                    , person: wrap (fromIntegral 1)
                                                                                                                                                                    , timeout: wrap (fromIntegral 100)
                                                                                                                                                                    })]
                                                                            , expiredCommitIds: mempty
                                                                            , redeemedPerPerson: mempty
                                                                            , timeoutData: Map.fromFoldable [(Tuple (wrap (fromIntegral 100)) (Set.fromFoldable [IdCommit (fromIntegral 1)]))] 
                                                                            }
                                                      , oracles: mempty
                                                      , usedIds: Set.fromFoldable [(wrap <<< fromIntegral $ 1), (wrap <<< fromIntegral $ 2)]
                                                      }
                                expectedTestState = set (_Newtype <<< _state) expectedState initialState
                            in
                                assertState expectedTestState finalState

assertState :: forall e. TestState -> TestState -> Test e
assertState a b = assert ("TestState not equal, expected: \n\n" <> show a <> "\n\n but got:\n\n" <> show b) $ a == b