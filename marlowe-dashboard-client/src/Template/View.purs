module Template.View
  ( templateLibraryCard
  , contractSetupScreen
  ) where

import Prelude hiding (div)
import Css (classNames)
import Data.Maybe (Maybe(..))
import Halogen.HTML (HTML, button, div, div_, h2_, h3_, h4_, p_, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), Screen(..))
import Template.Types (Template)

templateLibraryCard :: forall p. Array Template -> HTML p Action
templateLibraryCard templates =
  div_
    [ h2_ [ text "Start new from template" ]
    , div
        [ classNames [ "grid", "gap-1", "md:grid-cols-2", "lg:grid-cols-3" ] ]
        (templateBox <$> templates)
    ]

templateBox :: forall p. Template -> HTML p Action
templateBox template =
  div
    [ classNames [ "bg-white", "p-1" ] ]
    [ h4_
        [ text template.type_ ]
    , h3_
        [ text template.name ]
    , p_
        [ text template.description ]
    , button
        [ classNames [ "bg-green", "text-white" ]
        , onClick $ const $ Just $ SetScreen $ ContractSetupScreen template
        ]
        [ text "Setup" ]
    ]

contractSetupScreen :: forall p. Template -> HTML p Action
contractSetupScreen template =
  div
    [ classNames [ "p-1" ] ]
    [ text "Setup Contract" ]
