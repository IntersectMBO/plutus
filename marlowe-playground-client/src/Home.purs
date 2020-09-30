module Home where

import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (blocklyIcon, blocklyIconColour, flex, fullHeight, fullWidth, haskellIcon, horizontalFlip, marloweLogo, marloweLogo2, rightArrow, scroll, simulationIcon)
import Halogen.HTML (a, button, div, h1, h2, h3, img, input, label, p, text)
import Halogen.HTML.Events (onChecked)
import Halogen.HTML.Properties (InputType(..), checked, classes, href, id_, src, target, type_)
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
    , div [ classes [ flex, ClassName "start-with-container" ] ]
        [ div [ classes [ fullWidth ] ]
            [ h3 [] [ text "Option 1: Start with Haskell" ]
            , startWithHaskell state
            ]
        , div [ classes [ fullWidth ] ]
            [ h3 [] [ text "Option 2: Start with Marlowe or Blockly" ]
            , startWithMarlowe state
            ]
        ]
    , h3 [] [ text "Ready to go?" ]
    , div [ classes [ ClassName "ready-to-go-buttons" ] ]
        [ a [ href "./tutorial/index.html", target "_blank", classes [] ] [ text "Read our tutorial" ]
        , button [] [ text "Start coding!" ]
        ]
    , div [ classes [ ClassName "no-show-home" ] ]
        [ input [ id_ "no-show-home", type_ InputCheckbox, onChecked (Just <<< ShowHomePageInFuture <<< not), checked (state ^. (_showHomePage <<< to not)) ]
        , label [ HTML.for "no-show-home" ] [ text "Don’t show this screen next time" ]
        ]
    ]

startWithHaskell :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
startWithHaskell state =
  div [ classes [ ClassName "start-with-haskell" ] ]
    [ div []
        [ img [ src haskellIcon, classes [ ClassName "haskell-icon" ] ]
        , p [] [ text "Haskell" ]
        ]
    , div [ classes [ rightArrow ] ] []
    , marloweBlocklyBox state
    , div [ classes [ rightArrow ] ] []
    , div []
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p [] [ text "Simulator" ]
        ]
    ]

startWithMarlowe :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
startWithMarlowe state =
  div [ classes [ ClassName "start-with-marlowe" ] ]
    [ marloweBlocklyBox state
    , div [ classes [ rightArrow ] ] []
    , div []
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p [] [ text "Simulator" ]
        ]
    ]

marloweBlocklyBox :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
marloweBlocklyBox state =
  div [ classes [ ClassName "marlowe-blockly-box" ] ]
    [ div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src marloweLogo2 ]
        , p [] [ text "Marlowe" ]
        ]
    , div [ classes [ ClassName "arrows" ] ]
        [ div [ classes [ rightArrow ] ] []
        , div [ classes [ rightArrow, horizontalFlip ] ] []
        ]
    , div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src blocklyIconColour ]
        , p [] [ text "Blockly" ]
        ]
    ]
