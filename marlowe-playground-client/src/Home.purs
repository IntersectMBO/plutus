module Home where

import Data.Lens (to, (^.))
import Data.Maybe (Maybe(..))
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (blocklyIconColour, flex, fullHeight, fullWidth, haskellIcon, horizontalFlip, marloweLogo2, rightArrow, scroll, simulationIcon)
import Halogen.HTML (a, button, div, div_, h1_, h2_, h3_, img, input, label, p_, text)
import Halogen.HTML.Events (onChecked, onClick)
import Halogen.HTML.Properties (InputType(..), checked, classes, href, id_, src, target, type_)
import Halogen.HTML.Properties as HTML
import Prelude (const, not, (<<<))
import Types (ChildSlots, FrontendState, HAction(..), View(..), _showHomePage)

render :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
render state =
  div [ classes [ scroll, fullHeight ] ]
    [ h1_ [ text "What is the Marlowe Playground?" ]
    , p_ [ text "For Marlowe to be usable in practice, users need to be able to understand how contracts will behave once deployed to the blockchain, but without doing the deployment. We can do that by simulating their behaviour off-chain, interactively stepping through the evaluation of a contract in the browser-based tool, the Marlowe Playground, a web tool that supports the interactive construction, revision, and simulation of smart-contracts written in Marlowe." ]
    , h2_ [ text "How does the playground work?" ]
    , p_ [ text "Not sure what to put here" ]
    , div [ classes [ flex, ClassName "start-with-container" ] ]
        [ div [ classes [ fullWidth ] ]
            [ h3_ [ text "Option 1: Start with Haskell" ]
            , startWithHaskell state
            ]
        , div [ classes [ fullWidth ] ]
            [ h3_ [ text "Option 2: Start with Marlowe or Blockly" ]
            , startWithMarlowe state
            ]
        ]
    , h3_ [ text "Ready to go?" ]
    , div [ classes [ ClassName "ready-to-go-buttons" ] ]
        [ a [ href "./tutorial/index.html", target "_blank" ] [ text "Read our tutorial" ]
        , button [ onClick ((const <<< Just <<< ChangeView) Simulation) ] [ text "Start coding!" ]
        ]
    , div [ classes [ ClassName "no-show-home" ] ]
        [ input
            [ id_ "no-show-home"
            , type_ InputCheckbox
            , onChecked (Just <<< ShowHomePageInFuture <<< not)
            , checked (state ^. (_showHomePage <<< to not))
            ]
        , label [ HTML.for "no-show-home" ] [ text "Don’t show this screen next time" ]
        ]
    ]

startWithHaskell :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
startWithHaskell state =
  div [ classes [ ClassName "start-with-haskell" ] ]
    [ div []
        [ img [ src haskellIcon, classes [ ClassName "haskell-icon" ] ]
        , p_ [ text "Haskell" ]
        ]
    , div [ classes [ rightArrow ] ] []
    , marloweBlocklyBox state
    , div [ classes [ rightArrow ] ] []
    , div_
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p_ [ text "Simulator" ]
        ]
    ]

startWithMarlowe :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
startWithMarlowe state =
  div [ classes [ ClassName "start-with-marlowe" ] ]
    [ marloweBlocklyBox state
    , div [ classes [ rightArrow ] ] []
    , div_
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p_ [ text "Simulator" ]
        ]
    ]

marloweBlocklyBox :: forall m. FrontendState -> ComponentHTML HAction ChildSlots m
marloweBlocklyBox state =
  div [ classes [ ClassName "marlowe-blockly-box" ] ]
    [ div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src marloweLogo2 ]
        , p_ [ text "Marlowe" ]
        ]
    , div [ classes [ ClassName "arrows" ] ]
        [ div [ classes [ rightArrow ] ] []
        , div [ classes [ rightArrow, horizontalFlip ] ] []
        ]
    , div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src blocklyIconColour ]
        , p_ [ text "Blockly" ]
        ]
    ]
