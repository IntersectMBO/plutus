module Home where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (arrow, blocklyIconColour, downArrow, flex, haskellIcon, horizontalFlip, javascriptIcon, marloweLogo2, rightArrow, simulationIcon, vl)
import Halogen.HTML (HTML, a, button, div, div_, h2_, hr_, img, p_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, href, src, target)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State)

render :: forall m. State -> ComponentHTML Action ChildSlots m
render state =
  div [ classes [ ClassName "homepage-container" ] ]
    [ div [ classes [ ClassName "marlowe-intro-container" ] ]
        [ div [ classes [ ClassName "text-block" ] ]
            [ h2_ [ text "What is Marlowe?" ]
            , p_ [ text "Marlowe is special-purpose language for financial contracts on Cardano, allowing contracts to be written in the language of finance, rather than using a general-purpose language on the blockchain. Because it is special-purpose, it is easier to read, write and understand Marlowe contracts. It is also safer: some sorts of errors are impossible to write, and we can completely analyse contract behaviour without having to run a contract." ]
            ]
        , div [ classes [ ClassName "text-block" ] ]
            [ h2_ [ text "What is the Marlowe Playground?" ]
            , p_ [ text "In the browser-based Marlowe Playground you can write Marlowe contracts, in a variety of different ways. Once a contract is written, you can analyse its behaviour, e.g. checking whether any payments made by the contract could conceivably fail. You can also step through how a contract will behave, simulating the actions of the participants, and read a comprehensive tutorial on Marlowe and the Playground." ]
            ]
        , div [ classes [ ClassName "text-block" ] ]
            [ h2_ [ text "How does the playground work?" ]
            , p_ [ text "Marlowe contracts can be built in different ways. You can write them as Marlowe text, but also use the Blockly visual programming tool to create contracts by fitting together blocks that represent the different components. Marlowe is embedded in JavaScript and Haskell, and so you can use features from them to help you to build Marlowe contracts more readably and succinctly." ]
            ]
        ]
    , hr_
    , div [ classes [ flex, ClassName "start-with-container" ] ]
        [ startWith 1 "start with Haskell" startWithHaskell
        , startWith 2 "start with Javascript" startWithJavascript
        , startWith 3 "start with Marlowe or Blockly" startWithMarlowe
        ]
    , div [ classes [ ClassName "ready-to-go-buttons" ] ]
        [ h2_ [ text "Ready to go?" ]
        , button [ onClick ((const <<< Just <<< OpenModal) NewProject) ] [ text "Start a new project" ]
        , div [ classes [ ClassName "links" ] ]
            [ a [ href "./tutorial/index.html", target "_blank" ] [ text """Read our "Getting Started" guide""" ]
            , vl
            , a [ onClick ((const <<< Just <<< OpenModal) OpenDemo) ] [ text "Browse the example files" ]
            ]
        ]
    ]

startWith :: forall p. Int -> String -> HTML p Action -> HTML p Action
startWith index subtitle contents =
  div [ classes [ ClassName "start-with" ] ]
    [ h2_ [ text ("Option " <> show index) ]
    , p_ [ text subtitle ]
    , div [ classes [ ClassName "diagram" ] ] [ contents ]
    ]

downArrowBox :: forall p. HTML p Action
downArrowBox = div [ classes [ ClassName "fixed-height" ] ] [ div [ classes [ arrow, downArrow ] ] [] ]

simulationDiagram :: forall p. HTML p Action
simulationDiagram =
  div [ classes [ ClassName "group", flex, ClassName "simulation-group" ] ]
    [ downArrowBox
    , div_
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p_ [ text "Simulator" ]
        ]
    ]

startWithHaskell :: forall p. HTML p Action
startWithHaskell =
  div_
    [ div [ classes [ ClassName "group", flex, ClassName "compiler-group" ] ]
        [ div [ classes [ ClassName "icon-group" ] ]
            [ img [ src haskellIcon, classes [ ClassName "haskell-icon" ] ]
            , p_ [ text "Haskell" ]
            ]
        , downArrowBox
        ]
    , marloweBlocklyBox
    , simulationDiagram
    ]

startWithJavascript :: forall p. HTML p Action
startWithJavascript =
  div_
    [ div [ classes [ ClassName "group", flex, ClassName "compiler-group" ] ]
        [ div [ classes [ ClassName "icon-group" ] ]
            [ img [ src javascriptIcon, classes [ ClassName "javascript-icon" ] ]
            , p_ [ text "Javascript" ]
            ]
        , downArrowBox
        ]
    , marloweBlocklyBox
    , simulationDiagram
    ]

startWithMarlowe :: forall m. ComponentHTML Action ChildSlots m
startWithMarlowe =
  div_
    [ marloweBlocklyBox
    , div [ classes [ rightArrow ] ] []
    , simulationDiagram
    ]

marloweBlocklyBox :: forall p. HTML p Action
marloweBlocklyBox =
  div [ classes [ ClassName "marlowe-blockly-box" ] ]
    [ div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src marloweLogo2 ]
        , p_ [ text "Marlowe" ]
        ]
    , div [ classes [ ClassName "arrows" ] ]
        [ div [ classes [ arrow ] ] []
        , div [ classes [ arrow, horizontalFlip ] ] []
        ]
    , div [ classes [ ClassName "t-align-center" ] ]
        [ img [ src blocklyIconColour ]
        , p_ [ text "Blockly" ]
        ]
    ]
