module Library.View
  ( renderContractLibrary
  , renderContractDetails
  ) where

import Prelude hiding (div)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (div, text)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action, ChildSlots, ContractTemplate)

renderContractLibrary :: forall m. MonadAff m => Array ContractTemplate -> ComponentHTML Action ChildSlots m
renderContractLibrary contractTemplates =
  div
    [ classes $ ClassName <$> [ "p-1", "h-full", "overflow-auto" ] ]
    [ text "Quick Access" ]

renderContractDetails :: forall m. MonadAff m => ContractTemplate -> ComponentHTML Action ChildSlots m
renderContractDetails contractTemplate =
  div
    [ classes $ ClassName <$> [ "p-1", "h-full", "overflow-auto" ] ]
    [ text "Contract Template" ]
