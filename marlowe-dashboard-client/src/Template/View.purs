module Template.View
  ( renderTemplateLibrary
  , renderTemplateDetails
  ) where

import Prelude hiding (div)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (div, text)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action, ChildSlots, ContractTemplate)

renderTemplateLibrary :: forall m. MonadAff m => Array ContractTemplate -> ComponentHTML Action ChildSlots m
renderTemplateLibrary contractTemplates =
  div
    [ classes $ ClassName <$> [ "p-1", "h-full", "overflow-auto" ] ]
    [ text "Quick Access" ]

renderTemplateDetails :: forall m. MonadAff m => ContractTemplate -> ComponentHTML Action ChildSlots m
renderTemplateDetails contractTemplate =
  div
    [ classes $ ClassName <$> [ "p-1", "h-full", "overflow-auto" ] ]
    [ text "Contract Template" ]
