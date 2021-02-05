module Contract.View
  ( renderContractSetup
  , renderContractDetails
  ) where

import Prelude hiding (div)
import Css (classNames)
import Halogen.HTML (HTML, div, text)
import MainFrame.Types (Action, ContractInstance, ContractTemplate)

renderContractSetup :: forall p. ContractTemplate -> HTML p Action
renderContractSetup contractTemplate =
  div
    [ classNames [ "p-1" ] ]
    [ text "contract setup" ]

renderContractDetails :: forall p. ContractInstance -> HTML p Action
renderContractDetails contract =
  div
    [ classNames [ "p-1", "bg-gray" ] ]
    [ text "contract details" ]
