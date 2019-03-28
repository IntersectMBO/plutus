module StaticData
  ( bufferLocalStorageKey
  , demoFiles
  , marloweBufferLocalStorageKey
  , marloweContract
  , marloweContracts
  ) where

import Data.Map
  ( Map
  )
import Data.Tuple.Nested
  ( (/\)
  )
import Marlowe.Contracts
  ( crowdFunding
  , depositIncentive
  , escrow
  )
import Meadow.Contracts
  ( basicContract
  , zeroCouponBond
  )

import Data.Map as Map
import LocalStorage as LocalStorage

type Label
  = String

type Contents
  = String

demoFiles ::
  Map Label Contents
demoFiles = Map.fromFoldable [ "BasicContract" /\ basicContract
                             , "ZeroCouponBond" /\ zeroCouponBond
                             ]

marloweContracts ::
  Map Label Contents
marloweContracts = Map.fromFoldable [ "Deposit Incentive" /\ depositIncentive
                                    , "Crowd Funding" /\ crowdFunding
                                    , "Escrow" /\ escrow
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
