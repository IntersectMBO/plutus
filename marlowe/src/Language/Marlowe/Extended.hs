{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans       #-}

{-| = Extended Marlowe: adds templating functionality to Marlowe language
Extended Marlowe is not executable, it is translated to core Marlowe before
execution, deployment, or analysis, through the process of instantiation.
The purpose of Extended Marlowe is to allow Marlowe contracts to be reusable
in different situations without cluttering the code that goes on-chain
(core Marlowe).
-}

module Language.Marlowe.Extended ( module Language.Marlowe.Extended
                                 , module Language.Marlowe.Pretty
                                 , ada, adaSymbol, adaToken
                                 , S.AccountId, S.Bound(..), S.ChoiceId(..)
                                 , S.ChoiceName, S.ChosenNum, S.Party(..)
                                 , S.SlotInterval, S.Token(..), S.ValueId(..)
                                 ) where

import           GHC.Generics
import           Language.Marlowe.Pretty    (Pretty (..), pretty)
import qualified Language.Marlowe.Semantics as S
import           Language.Marlowe.Util      (ada)
import           Ledger.Ada                 (adaSymbol, adaToken)
import           Text.PrettyPrint.Leijen    (parens, text)


data Timeout = SlotParam String
             | Slot Integer
  deriving stock (Show,Generic)

instance Pretty Timeout where
    prettyFragment (Slot n)         = prettyFragment n
    prettyFragment sp@(SlotParam _) = parens $ text $ show sp

instance Num Timeout where
  (+) (Slot a) (Slot b) = Slot (a + b)
  (+) _ _               = error "Tried to add with templates"
  (-) (Slot a) (Slot b) = Slot (a - b)
  (-) _ _               = error "Tried to subtract with templates"
  (*) (Slot a) (Slot b) = Slot (a * b)
  (*) _ _               = error "Tried to multiplate with templates"
  abs (Slot a) = Slot (abs a)
  abs _        = error "Tried to calculate absolute value of template"
  signum (Slot a) = Slot (signum a)
  signum _        = error "Tried to calculate signum of template"
  fromInteger x = Slot x
  negate (Slot x) = Slot (-x)
  negate _        = error "Tried to negate a template"

instance Pretty Rational where
    prettyFragment = text . show

data Value = AvailableMoney S.AccountId S.Token
           | Constant Integer
           | ConstantParam String
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | MulValue Value Value
           | Scale Rational Value
           | ChoiceValue S.ChoiceId
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue S.ValueId
           | Cond Observation Value Value
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)

data Observation = AndObs Observation Observation
                 | OrObs Observation Observation
                 | NotObs Observation
                 | ChoseSomething S.ChoiceId
                 | ValueGE Value Value
                 | ValueGT Value Value
                 | ValueLT Value Value
                 | ValueLE Value Value
                 | ValueEQ Value Value
                 | TrueObs
                 | FalseObs
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)

data Action = Deposit S.AccountId S.Party S.Token Value
            | Choice S.ChoiceId [S.Bound]
            | Notify Observation
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)

data Payee = Account S.AccountId
           | Party S.Party
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)

data Case = Case Action Contract
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)

data Contract = Close
              | Pay S.AccountId Payee S.Token Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let S.ValueId Value Contract
              | Assert Observation Contract
  deriving stock (Show,Generic)
  deriving anyclass (Pretty)
