module Home where

import Prelude hiding (div)
import Auth (_GithubUser, authStatusAuthRole)
import Data.Lens (has)
import Data.Maybe (Maybe(..))
import Halogen (ComponentHTML)
import Halogen.Classes (arrowLeftDown, arrowLeftUp, arrowRightDown, arrowRightUp, marloweLogo, newProjectBlocklyIcon, newProjectHaskellIcon, newProjectJavascriptIcon, primaryButton, secondaryButton, simulationIconBlack)
import Halogen.Css (classNames)
import Halogen.HTML (a, button, div, h1, img, span, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (href, src, target)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, _authStatus)
import Network.RemoteData (_Success)
import NewProject.Types as NewProject
import Projects.Types (Lang(..))

render :: forall m. State -> ComponentHTML Action ChildSlots m
render state =
  div [ classNames [ "flex", "flex-col", "items-center", "my-16" ] ]
    [ h1 [ classNames [ "font-semibold", "text-4xl", "mb-16" ] ] [ text "Get started" ]
    , div [ classNames [ "mb-6" ] ]
        [ button
            [ classNames (secondaryButton <> [ "mr-small", "w-56", "text-base", "cursor-pointer" ])
            , onClick \_ ->
                if has (_authStatus <<< _Success <<< authStatusAuthRole <<< _GithubUser) state then
                  Just $ OpenModal OpenProject
                else
                  Just $ OpenModal $ GithubLogin (OpenModal OpenProject)
            ]
            [ text "Open existing project" ]
        , button
            [ classNames (primaryButton <> [ "ml-small", "w-56", "text-base", "cursor-pointer" ])
            , onClick ((const <<< Just <<< OpenModal) OpenDemo)
            ]
            [ text "Open an example" ]
        ]
    , span [ classNames [ "text-base", "mb-4" ] ] [ text "Or" ]
    , div [ classNames [ "mb-16", "text-base" ] ]
        [ span [ classNames [ "font-bold" ] ] [ text "Choose" ]
        , span_ [ text " a starting environment that's right for you." ]
        ]
    , div
        [ classNames [ "flex", "mb-8" ] ]
        [ div
            [ classNames (newProjectClasses <> [ "mr-24" ])
            , onClick (const <<< Just $ NewProjectAction $ NewProject.CreateProject Javascript)
            ]
            [ img [ src newProjectJavascriptIcon, classNames [ "h-16", "mb-4" ] ]
            , text
                "Start in Javascript"
            ]
        , div
            [ classNames (newProjectClasses <> [ "mr-24" ])
            , onClick (const <<< Just $ NewProjectAction $ NewProject.CreateProject Haskell)
            ]
            [ img [ src newProjectHaskellIcon, classNames [ "h-16", "mb-4" ] ]
            , text
                "Start in Haskell"
            ]
        , div [ classNames [ "border-0", "border-l", "border-black", "border-solid", "h-10", "mt-2" ] ] []
        , div
            [ classNames (newProjectClasses <> [ "ml-24", "mr-4" ])
            , onClick (const <<< Just $ NewProjectAction $ NewProject.CreateProject Marlowe)
            ]
            [ img [ src marloweLogo, classNames [ "h-16", "mb-4" ] ]
            , text
                "Start in Marlowe"
            ]
        , div [ classNames [ "flex", "flex-col" ] ]
            [ img [ classNames [ "mt-4" ], src arrowRightUp ]
            , img [ classNames [ "mt-3" ], src arrowLeftUp ]
            ]
        , div
            [ classNames (newProjectClasses <> [ "ml-4", "mr-1" ])
            , onClick (const <<< Just $ NewProjectAction $ NewProject.CreateProject Blockly)
            ]
            [ img [ src newProjectBlocklyIcon, classNames [ "h-16", "mb-4" ] ]
            , text
                "Start in Blockly"
            ]
        ]
    , div [ classNames [ "mb-10", "flex", "items-end" ] ]
        [ img [ classNames [ "mr-24" ], src arrowRightDown ]
        , div [ classNames [ "flex", "flex-col", "text-sm" ] ]
            [ img [ src simulationIconBlack, classNames [ "mb-4" ] ]
            , text "Simulate"
            ]
        , img [ classNames [ "ml-24" ], src arrowLeftDown ]
        ]
    , div [ classNames [ "font-bold", "text-sm" ] ]
        [ a [ href "./doc/marlowe/tutorials/index.html", target "_blank" ] [ text "Read our Getting Started guide" ]
        ]
    ]
  where
  newProjectClasses = [ "flex", "flex-col", "font-bold", "text-sm", "cursor-pointer", "text-center" ]
