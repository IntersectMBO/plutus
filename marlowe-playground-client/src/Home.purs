module Home where

import Data.Maybe (Maybe(..))
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (blocklyIconColour, flex, fullWidth, haskellIcon, horizontalFlip, javascriptIcon, marloweLogo2, rightArrow, scroll, simulationIcon)
import Halogen.HTML (button, div, div_, h2_, h3_, img, p_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, src)
import Prelude (const, (<<<))
import MainFrame.Types (ModalView(..), Action(..), ChildSlots, FrontendState)

render :: forall m. FrontendState -> ComponentHTML Action ChildSlots m
render state =
  div [ classes [ scroll, ClassName "homepage-container" ] ]
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
            , p_ [ text "Marlowe contracts can be built in different ways. You can write them as Marlowe text, but also use the Blockly visual programming tool to create contracts by fitting together blocks that represent the different components. Marlowe is written in the Haskell programming language, and you can also use Haskell features to help you describe Marlowe contracts more readably and succinctly." ]
            ]
        ]
    , div [ classes [ flex, ClassName "start-with-container" ] ]
        [ div [ classes [ fullWidth, flex ] ]
            [ div [ class_ (ClassName "even-item") ] []
            , startWithHaskell state
            , div [ class_ (ClassName "even-item") ] []
            ]
        ]
    , div [ classes [ ClassName "home-buttons" ] ]
        [ div [ classes [ ClassName "ready-to-go-buttons" ] ]
            [ button [ onClick ((const <<< Just <<< OpenModal) NewProject) ] [ text "Start coding!" ]
            ]
        ]
    ]

startWithHaskell :: forall m. FrontendState -> ComponentHTML Action ChildSlots m
startWithHaskell state =
  div [ classes [ ClassName "start-with-haskell", ClassName "even-item" ] ]
    [ div [ classes [ ClassName "group", ClassName "compilers-group" ] ]
        [ div [ classes [ ClassName "group", flex, ClassName "compiler-group" ] ]
            [ div [ classes [ ClassName "icon-group" ] ]
                [ img [ src haskellIcon, classes [ ClassName "haskell-icon" ] ]
                , p_ [ text "Haskell" ]
                ]
            , div [ classes [ rightArrow ] ] []
            ]
        , div [ classes [ ClassName "group", flex, ClassName "compiler-group" ] ]
            [ div [ classes [ ClassName "icon-group" ] ]
                [ img [ src javascriptIcon, classes [ ClassName "javascript-icon" ] ]
                , p_ [ text "Javascript" ]
                ]
            , div [ classes [ rightArrow ] ] []
            ]
        ]
    , marloweBlocklyBox state
    , div [ classes [ ClassName "group", flex, ClassName "simulation-group" ] ]
        [ div [ classes [ rightArrow ] ] []
        , div_
            [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
            , p_ [ text "Simulator" ]
            ]
        ]
    ]

startWithMarlowe :: forall m. FrontendState -> ComponentHTML Action ChildSlots m
startWithMarlowe state =
  div [ classes [ ClassName "start-with-marlowe" ] ]
    [ marloweBlocklyBox state
    , div [ classes [ rightArrow ] ] []
    , div_
        [ img [ src simulationIcon, classes [ ClassName "sim-icon" ] ]
        , p_ [ text "Simulator" ]
        ]
    ]

marloweBlocklyBox :: forall m. FrontendState -> ComponentHTML Action ChildSlots m
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
