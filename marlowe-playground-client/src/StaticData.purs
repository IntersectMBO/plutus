module StaticData
  ( bufferLocalStorageKey
  , jsBufferLocalStorageKey
  , demoFiles
  , demoFilesJS
  , marloweBufferLocalStorageKey
  , marloweContract
  , marloweContracts
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Semigroup ((<>))
import Data.Tuple.Nested ((/\), type (/\))
import Examples.Haskell.Contracts (escrow, zeroCouponBond, couponBondGuaranteed, swap) as HE
import Examples.Marlowe.Contracts (escrow, zeroCouponBond, option, swap) as ME
import Examples.JS.Contracts (escrow, zeroCouponBond, couponBondGuaranteed, swap) as JSE
import LocalStorage as LocalStorage

type Label
  = String

type Contents
  = String

demoFiles ::
  Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "Escrow" /\ HE.escrow
    , "ZeroCouponBond" /\ HE.zeroCouponBond
    , "CouponBondGuaranteed" /\ HE.couponBondGuaranteed
    , "Swap" /\ HE.swap
    ]

addHeader :: Contents -> Contents
addHeader c =
  """import * as bignumber from 'bignumber.js';
import { role, accountId, choiceId, token, ada, valueId, availableMoney, constant, 
         negValue, addValue, subValue, mulValue, scale, choiceValue, slotIntervalStart, 
         slotIntervalEnd, useValue, cond, andObs, orObs, notObs, choseSomething, valueGE, 
         valueGT, valueLT, valueLE, valueEQ, trueObs, falseObs, bound, deposit, choice, 
         notify, caseM, closeM, payM, ifM, whenM, letM, assertM, Party, SomeNumber,
         AccountId, ChoiceId, Token, ValueId, Value, EValue, Observation, Bound, Action,
         Payee, Case, Contract } from 'marlowe-js';

/* === Code above this comment will be removed at compile time === */

"""
    <> c

demoFilesJS ::
  Map Label Contents
demoFilesJS =
  Map.fromFoldable
    [ "Escrow" /\ addHeader JSE.escrow
    , "ZeroCouponBond" /\ addHeader JSE.zeroCouponBond
    , "CouponBondGuaranteed" /\ addHeader JSE.couponBondGuaranteed
    , "Swap" /\ addHeader JSE.swap
    ]

marloweContracts ::
  Array (Label /\ Contents)
marloweContracts =
  [ "Escrow" /\ ME.escrow
  , "ZeroCouponBond" /\ ME.zeroCouponBond
  , "Option" /\ ME.option
  , "Swap" /\ ME.swap
  , "Empty" /\ "?empty_contract"
  ]

marloweContract ::
  Contents
marloweContract = "(Some Marlowe Code)"

bufferLocalStorageKey ::
  LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "PlutusPlaygroundBuffer"

jsBufferLocalStorageKey ::
  LocalStorage.Key
jsBufferLocalStorageKey = LocalStorage.Key "JavascriptBuffer"

marloweBufferLocalStorageKey ::
  LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"
