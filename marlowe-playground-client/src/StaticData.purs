module StaticData (bufferLocalStorageKey, demoFiles, marloweBufferLocalStorageKey, marloweContract, marloweContracts) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\), type (/\))
import Examples.Haskell.Contracts (escrow, zeroCouponBond, couponBondGuaranteed, swap) as HE
import Examples.Marlowe.Contracts (escrow, zeroCouponBond, couponBondGuaranteed, swap) as ME
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

marloweContracts ::
  Array (Label /\ Contents)
marloweContracts =
  [ "Escrow" /\ ME.escrow
  , "ZeroCouponBond" /\ ME.zeroCouponBond
  , "CouponBondGuaranteed" /\ ME.couponBondGuaranteed
  , "Swap" /\ ME.swap
  , "Empty" /\ "?empty_contract"
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
