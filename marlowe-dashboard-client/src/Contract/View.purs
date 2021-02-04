module Contract.View
  ( renderContractSetup
  , renderRunningContract
  ) where

import Prelude hiding (div)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (div, text)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action, ChildSlots, Contract, ContractTemplate)

renderContractSetup :: forall m. MonadAff m => ContractTemplate -> ComponentHTML Action ChildSlots m
renderContractSetup contractTemplate =
  div
    [ classes $ ClassName <$> [ "p-1" ] ]
    [ text "contract setup" ]

renderRunningContract :: forall m. MonadAff m => Contract -> ComponentHTML Action ChildSlots m
renderRunningContract contract =
  div
    [ classes $ ClassName <$> [ "p-1", "bg-gray" ] ]
    [ text "running contract" ]
