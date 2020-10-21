module StaticData
  ( bufferLocalStorageKey
  , jsBufferLocalStorageKey
  , demoFiles
  , demoFilesJS
  , marloweBufferLocalStorageKey
  , marloweContract
  , marloweContracts
  , showHomePageLocalStorageKey
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Semigroup ((<>))
import Data.Tuple.Nested ((/\), type (/\))
import Examples.Haskell.Contracts (contractForDifference, escrow, zeroCouponBond, couponBondGuaranteed, swap) as HE
import Examples.Marlowe.Contracts (contractForDifference, escrow, zeroCouponBond, option, swap) as ME
import Examples.JS.Contracts (cfd, escrow, zeroCouponBond, couponBondGuaranteed, swap) as JSE
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
    , "CFD" /\ HE.contractForDifference
    ]

addHeader :: Contents -> Contents
addHeader c =
  """import { PK, Role, Account, Party, ada, AvailableMoney, Constant, NegValue, AddValue,
         SubValue, MulValue, Scale, ChoiceValue, SlotIntervalStart, SlotIntervalEnd,
         UseValue, Cond, AndObs, OrObs, NotObs, ChoseSomething, ValueGE, ValueGT,
         ValueLT, ValueLE, ValueEQ, TrueObs, FalseObs, Deposit, Choice, Notify,
         Close, Pay, If, When, Let, Assert, SomeNumber, AccountId, ChoiceId, Token,
         ValueId, Value, EValue, Observation, Bound, Action, Payee, Case, Contract } from 'marlowe-js';

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
    , "CFD" /\ addHeader JSE.cfd
    ]

marloweContracts ::
  Array (Label /\ Contents)
marloweContracts =
  [ "Escrow" /\ ME.escrow
  , "ZeroCouponBond" /\ ME.zeroCouponBond
  , "Option" /\ ME.option
  , "Swap" /\ ME.swap
  , "CFD" /\ ME.contractForDifference
  , "Empty" /\ "?empty_contract"
  ]

marloweContract ::
  Contents
marloweContract = "(Some Marlowe Code)"

bufferLocalStorageKey ::
  LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "HaskellBuffer"

jsBufferLocalStorageKey ::
  LocalStorage.Key
jsBufferLocalStorageKey = LocalStorage.Key "JavascriptBuffer"

marloweBufferLocalStorageKey ::
  LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"

showHomePageLocalStorageKey ::
  LocalStorage.Key
showHomePageLocalStorageKey = LocalStorage.Key "ShowHomePage"
