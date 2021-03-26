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
import Examples.Haskell.Contracts (contractForDifferences, couponBondGuaranteed, escrow, escrowWithCollateral, example, swap, zeroCouponBond) as HE
import Examples.JS.Contracts (contractForDifferences, couponBondGuaranteed, escrow, escrowWithCollateral, example, swap, zeroCouponBond) as JSE
import Examples.Marlowe.Contracts (contractForDifferences, couponBondGuaranteed, escrow, escrowWithCollateral, example, swap, zeroCouponBond) as ME
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
    , "EscrowWithCollateral" /\ HE.escrowWithCollateral
    , "ZeroCouponBond" /\ HE.zeroCouponBond
    , "CouponBondGuaranteed" /\ HE.couponBondGuaranteed
    , "Swap" /\ HE.swap
    , "CFD" /\ HE.contractForDifferences
    ]

demoFilesJS ::
  Map Label Contents
demoFilesJS =
  Map.fromFoldable
    [ "Example" /\ JSE.example
    , "Escrow" /\ JSE.escrow
    , "EscrowWithCollateral" /\ JSE.escrowWithCollateral
    , "ZeroCouponBond" /\ JSE.zeroCouponBond
    , "CouponBondGuaranteed" /\ JSE.couponBondGuaranteed
    , "Swap" /\ JSE.swap
    , "CFD" /\ JSE.contractForDifferences
    ]

marloweContracts ::
  Map Label Contents
marloweContracts =
  Map.fromFoldable
    [ "Example" /\ ME.example
    , "Escrow" /\ ME.escrow
    , "EscrowWithCollateral" /\ ME.escrowWithCollateral
    , "ZeroCouponBond" /\ ME.zeroCouponBond
    , "CouponBondGuaranteed" /\ ME.couponBondGuaranteed
    , "Swap" /\ ME.swap
    , "CFD" /\ ME.contractForDifferences
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
