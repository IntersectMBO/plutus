module Home where

import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen (ComponentHTML)
import Halogen.Classes (flex, fullHeight, fullWidth, scroll)
import Halogen.HTML (a, div, h1, h2, h3, input, label, p, text)
import Halogen.HTML.Events (onChecked)
import Halogen.HTML.Properties (InputType(..), checked, classes, id_, type_)
import Halogen.HTML.Properties as HTML
import Prelude (not, (<<<))
import Types (ChildSlots, FrontendState, HAction(..), _showHomePage)

render :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
render state =
  div [ classes [ scroll, fullHeight ] ]
    [ h1 [] [ text "What is the Marlowe Playground?" ]
    , p [] [ text "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction. Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction. Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction." ]
    , p [] [ text "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction." ]
    , h2 [] [ text "How does the playground work?" ]
    , p [] [ text "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction. Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties." ]
    , div [ classes [ flex ] ]
        [ div [ classes [ fullWidth ] ]
            [ h3 [] [ text "Option 1: Start with Haskell" ]
            ]
        , div [ classes [ fullWidth ] ]
            [ h3 [] [ text "Option 2: Start with Marlowe or Blockly" ]
            ]
        ]
    , h3 [] [ text "Ready to go?" ]
    , a [] [ text "Read our tutorial" ]
    , a [] [ text "Start coding!" ]
    , div []
        [ input [ id_ "no-show-home", type_ InputCheckbox, onChecked (Just <<< ShowHomePageInFuture <<< not), checked (state ^. (_showHomePage <<< to not)) ]
        , label [ HTML.for "no-show-home" ] [ text "Don’t show this screen next time" ]
        ]
    ]
