{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Spec.Marlowe.Common where

import           Data.Map.Strict            (Map)

import           Hedgehog                   (Gen, Size (..))
import           Hedgehog.Gen               (choice, element, integral, sized)
import qualified Hedgehog.Range             as Range

import           Language.Marlowe.Semantics
import qualified Ledger
import qualified Ledger.Ada                 as Ada
import           Wallet                     (PubKey (..))

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map PubKey Ledger.Value }

amount :: Gen Integer
amount = integral (Range.linear (-100) 100)


positiveAmount :: Gen Integer
positiveAmount = integral (Range.linear 1 100)


boundedValue :: [Party] -> [ChoiceId] -> Gen Value
boundedValue parties choices = sized $ boundedValueAux parties choices


boundedValueAux :: [Party] -> [ChoiceId] -> Size -> Gen Value
boundedValueAux parties choices (Size s) = do
    let accounts  = [AccountId 0 p | p <- parties]
    let go s      = boundedValueAux parties choices (Size s)
    let anyChoice = ChoiceId "choice" <$> element parties
    let choiceId  = if null choices then anyChoice else choice [element choices, anyChoice]
    case compare s 0 of
        GT -> choice [ AvailableMoney <$> element accounts <*> pure (Token Ada.adaSymbol Ada.adaToken)
                    , NegValue <$> go (s `div` 2)
                    , (AddValue <$> go (s `div` 2)) <*> go (s `div` 2)
                    , (SubValue <$> go (s `div` 2)) <*> go (s `div` 2)
                    , Constant <$> amount
                    , ChoiceValue <$> choiceId <*> go (s - 1) ]
        EQ -> choice [ AvailableMoney <$> element accounts <*> pure (Token Ada.adaSymbol Ada.adaToken)
                     , Constant <$> amount ]
        LT -> error "Negative size in boundedValue"
