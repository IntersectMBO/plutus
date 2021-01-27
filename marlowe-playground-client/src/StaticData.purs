module StaticData
  ( haskellBufferLocalStorageKey
  , jsBufferLocalStorageKey
  , demoFiles
  , demoFilesJS
  , marloweBufferLocalStorageKey
  , simulatorBufferLocalStorageKey
  , marloweContract
  , marloweContracts
  , gistIdLocalStorageKey
  , sessionStorageKey
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Examples.Haskell.Contracts (contractForDifference, couponBondGuaranteed, escrow, example, swap, zeroCouponBond) as HE
import Examples.JS.Contracts (cfd, couponBondGuaranteed, escrow, example, swap, zeroCouponBond) as JSE
import Examples.Marlowe.Contracts (contractForDifference, escrow, example, option, swap, zeroCouponBond) as ME
import LocalStorage as LocalStorage

type Label
  = String

type Contents
  = String

demoFiles ::
  Map Label Contents
demoFiles =
  Map.fromFoldable
    [ "Example" /\ HE.example
    , "Escrow" /\ HE.escrow
    , "ZeroCouponBond" /\ HE.zeroCouponBond
    , "CouponBondGuaranteed" /\ HE.couponBondGuaranteed
    , "Swap" /\ HE.swap
    , "CFD" /\ HE.contractForDifference
    ]

demoFilesJS ::
  Map Label Contents
demoFilesJS =
  Map.fromFoldable
    [ "Example" /\ JSE.example
    , "Escrow" /\ JSE.escrow
    , "ZeroCouponBond" /\ JSE.zeroCouponBond
    , "CouponBondGuaranteed" /\ JSE.couponBondGuaranteed
    , "Swap" /\ JSE.swap
    , "CFD" /\ JSE.cfd
    ]

marloweContracts ::
  Map Label Contents
marloweContracts =
  Map.fromFoldable
    [ "Example" /\ ME.example
    , "Escrow" /\ ME.escrow
    , "ZeroCouponBond" /\ ME.zeroCouponBond
    , "Option" /\ ME.option
    , "Swap" /\ ME.swap
    , "CFD" /\ ME.contractForDifference
    ]

marloweContract ::
  Contents
marloweContract = "(Some Marlowe Code)"

haskellBufferLocalStorageKey ::
  LocalStorage.Key
haskellBufferLocalStorageKey = LocalStorage.Key "HaskellBuffer"

jsBufferLocalStorageKey ::
  LocalStorage.Key
jsBufferLocalStorageKey = LocalStorage.Key "JavascriptBuffer"

marloweBufferLocalStorageKey ::
  LocalStorage.Key
marloweBufferLocalStorageKey = LocalStorage.Key "MarloweBuffer"

simulatorBufferLocalStorageKey ::
  LocalStorage.Key
simulatorBufferLocalStorageKey = LocalStorage.Key "SimulationBuffer"

gistIdLocalStorageKey ::
  LocalStorage.Key
gistIdLocalStorageKey = LocalStorage.Key "GistId"

sessionStorageKey :: LocalStorage.Key
sessionStorageKey = LocalStorage.Key "MarlowePlaygroundSession"
