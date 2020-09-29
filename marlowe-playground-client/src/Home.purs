module Home where

import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (flex, fullWidth)
import Halogen.HTML (a, div, h1, h2, h3, input, p, text)
import Halogen.HTML.Properties (class_, classes, id_)
import Types (ChildSlots, FrontendState, HAction)

render :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
render state =
  div []
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
    , input [ id_ "no-show-home" ]
    ]
