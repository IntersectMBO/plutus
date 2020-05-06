{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Spec.Marlowe.Common where

import           Data.Map.Strict         (Map)

import           Hedgehog                (Gen, Size (..))
import           Hedgehog.Gen            (choice, element, integral, sized)
import qualified Hedgehog.Range          as Range

import           Language.Marlowe
import           Language.PlutusTx.Ratio
import           Ledger                  (pubKeyHash)
import qualified Ledger                  as Ledger
import qualified Ledger.Ada              as Ada
import           Ledger.Value            (CurrencySymbol (..), TokenName (..))
import           Wallet                  (PubKey (..))
import           Wallet.Emulator

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map PubKey Ledger.Value }

amount :: Gen Integer
amount = integral (Range.constantFrom 0 (-100) 100)


positiveAmount :: Gen Integer
positiveAmount = integral (Range.constant 1 100)

partyGen :: Gen Party
partyGen = choice [ return $ Role "alice"
                 , return $ PK (Ledger.pubKeyHash "6361726f6c")
                 ]


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


pangramContract :: Contract
pangramContract = let
    alicePk = PK $ (pubKeyHash $ walletPubKey (Wallet 1))
    aliceAcc = AccountId 0 alicePk
    bobRole = Role "Bob"
    constant = Constant 100
    choiceId = ChoiceId "choice" alicePk
    token = Token (CurrencySymbol "aa") (TokenName "name")
    valueExpr = AddValue constant (SubValue constant (NegValue constant))
    in When
        [ Case (Deposit aliceAcc alicePk ada valueExpr)
            (Let (ValueId "x") valueExpr
                (Pay aliceAcc (Party bobRole) ada (UseValue (ValueId "x")) Close))
        , Case (Choice choiceId [Bound 0 1, Bound 10 20])
            (If (ChoseSomething choiceId `OrObs` (ChoiceValue choiceId constant `ValueEQ` Scale (1 % 10) constant))
                (Pay aliceAcc (Account aliceAcc) token (AvailableMoney aliceAcc token) Close)
                Close)
        , Case (Notify (AndObs (SlotIntervalStart `ValueLT` SlotIntervalEnd) TrueObs)) Close
        ] (Slot 100) Close
