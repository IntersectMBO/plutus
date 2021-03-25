module ContractHome.State
  ( defaultState
  , handleAction
  ) where

import Prelude
import Contract.State (mkInitialState) as Contract
import Contract.Types (State) as Contract
import ContractHome.Lenses (_selectedContract, _status)
import ContractHome.Types (ContractStatus(..), State, Action(..))
import Data.Array (catMaybes)
import Data.BigInteger (fromInt)
import Data.Lens (assign)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Halogen (HalogenM)
import Marlowe.Extended (TemplateContent(..), fillTemplate, toCore)
import Marlowe.Market.Contract1 as Contract1
import Marlowe.Market.Contract3 as Contract3
import Marlowe.Semantics (Party(..))

-- FIXME: debug purposes only, delete later
filledContract1 :: Maybe Contract.State
filledContract1 =
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "Buyer's deposit timeout" /\ fromInt 10
              , "Buyer's dispute timeout" /\ fromInt 12
              , "Seller's response timeout" /\ fromInt 15
              , "Timeout for arbitrage" /\ fromInt 17
              ]
        , valueContent:
            Map.fromFoldable
              [ "Price" /\ fromInt 1500
              ]
        }

    participants =
      Map.fromFoldable
        [ (Role "Arbiter") /\ Just "Alice user"
        , (Role "Buyer") /\ Just "Bob user"
        , (Role "Seller") /\ Nothing
        ]

    mContract = toCore $ fillTemplate templateContent Contract1.extendedContract
  in
    mContract <#> \contract -> Contract.mkInitialState zero contract Contract1.metaData participants (Just $ Role "Arbiter")

{-
filledContract2 :: Maybe Contract.State
filledContract2 =
  let
    templateContent =
      TemplateContent
        { slotContent:
            Map.fromFoldable
              [ "aliceTimeout" /\ fromInt 10
              , "arbitrageTimeout" /\ fromInt 12
              , "bobTimeout" /\ fromInt 15
              , "depositSlot" /\ fromInt 17
              ]
        , valueContent:
            Map.fromFoldable
              [ "amount" /\ fromInt 1500
              ]
        }

    mContract = toCore $ fillTemplate templateContent Contract3.extendedContract
  in
    mContract <#> \contract -> Contract.mkInitialState zero contract Contract3.metaData
-}
defaultState :: State
defaultState =
  { status: Running
  , contracts: catMaybes [ filledContract1 ]
  -- , contracts: mempty
  , selectedContract: Nothing
  }

handleAction ::
  forall m slots msg.
  Action -> HalogenM State Action slots msg m Unit
handleAction ToggleTemplateLibraryCard = pure unit -- handled in Play

handleAction (SelectView view) = assign _status view

handleAction (OpenContract contract) = assign _selectedContract $ Just contract
