module Template.View
  ( templateLibraryCard
  , templateDetailsCard
  , templateSetupScreen
  ) where

import Prelude hiding (div)
import Css (classNames)
import Halogen.HTML (HTML, div, text)
import MainFrame.Types (Action, ContractTemplate)

templateLibraryCard :: forall p. HTML p Action
templateLibraryCard =
  div
    [ classNames [ "h-full", "overflow-auto" ] ]
    [ text "Start new from template" ]

templateDetailsCard :: forall p. ContractTemplate -> HTML p Action
templateDetailsCard contractTemplate =
  div
    [ classNames [ "h-full", "overflow-auto" ] ]
    [ text "Contract Template" ]

templateSetupScreen :: forall p. ContractTemplate -> HTML p Action
templateSetupScreen contractTemplate =
  div
    [ classNames [ "h-full", "overflow-auto" ] ]
    [ text "Setup Contract" ]
