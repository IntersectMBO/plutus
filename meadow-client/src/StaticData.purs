module StaticData (bufferLocalStorageKey, demoFiles, marloweBufferLocalStorageKey, marloweContract, marloweContracts) where

import Data.Map (Map)
import Data.Tuple.Nested ((/\))
import Marlowe.Contracts (crowdFunding, depositIncentive, escrow) as S
import Meadow.Contracts (escrow, zeroCouponBond, couponBondGuaranteed) as E
import Data.Map as Map
import LocalStorage as LocalStorage

type Label
  = String

type Contents
  = String

demoFiles ::
  Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "Escrow" /\ E.escrow
    , "ZeroCouponBond" /\ E.zeroCouponBond
    , "CouponBondGuaranteed" /\ E.couponBondGuaranteed
    ]

marloweContracts ::
  Map Label Contents
marloweContracts =
  Map.fromFoldable
    [ "Deposit Incentive" /\ S.depositIncentive
    , "Crowd Funding" /\ S.crowdFunding
    , "Escrow" /\ S.escrow
    ]

marloweContract ::
  Contents
marloweContract = "(Some Marlowe Code)"

bufferLocalStorageKey ::
  LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "PlutusPlaygroundBuffer"

marloweBufferLocalStorageKey ::
  LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"
