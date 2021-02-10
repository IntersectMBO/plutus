module Template.View
  ( renderTemplateLibrary
  , renderTemplateDetails
  ) where

import Prelude hiding (div)
import Css (classNames)
import Halogen.HTML (HTML, div, text)
import MainFrame.Types (Action, ContractTemplate)

renderTemplateLibrary :: forall p. Array ContractTemplate -> HTML p Action
renderTemplateLibrary contractTemplates =
  div
    [ classNames [ "h-full", "overflow-auto" ] ]
    [ text "Start new from template" ]

renderTemplateDetails :: forall p. ContractTemplate -> HTML p Action
renderTemplateDetails contractTemplate =
  div
    [ classNames [ "h-full", "overflow-auto" ] ]
    [ text "Contract Template" ]
