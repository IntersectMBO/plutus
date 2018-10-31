module MainFrame
  ( mainFrame
  , Query
  ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, AceMessage(..), AceQuery, aceComponent)
import Ace.Types (ACE, Editor)
import Bootstrap (btnPrimary, btnSecondary, container)
import Control.Monad.Aff (Aff)
import Control.Monad.Eff.Class (liftEff)
import Data.Lens (Lens', modifying)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Debug.Trace
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), HTML, button, div, h1_, h3_, hr_, slot, small_, text)
import Halogen.HTML.Events (input, input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Halogen.Query (HalogenM)
import Prelude (class Eq, class Ord, type (~>), Unit, Void, bind, const, discard, not, pure, unit, void, ($))

data Query a
  = ToggleState a
  | HandleAceOutput AceMessage a

type State =
  { on :: Boolean }

_on :: forall s a. Lens' {on :: a | s} a
_on = prop (SProxy :: SProxy "on")

initialState :: State
initialState = { on: false }

initialText :: String
initialText = """{-# LANGUAGE TemplatePlutus #-}

module Main where

main :: IO ()
main = do
  putStrLn "Hello"
  putStrLn "Plutus"
"""
------------------------------------------------------------

data Slot
  = AceComponent

derive instance eqComponentSlot :: Eq Slot
derive instance ordComponentSlot :: Ord Slot

------------------------------------------------------------

mainFrame :: forall aff. Component HTML Query Unit Void (Aff (AceEffects aff))
mainFrame =
  H.parentComponent
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }

eval :: forall m. Query ~> HalogenM State Query AceQuery Slot Void m
eval (ToggleState next) = do
  modifying _on not
  pure next

eval (HandleAceOutput (TextChanged msg) next) = do
  void $ traceAnyM msg
  pure next

------------------------------------------------------------
initEditor ∷ forall aff. Editor -> Aff (ace :: ACE | aff) Unit
initEditor editor = liftEff $ do
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session
  void $ Editor.setValue initialText (Just 1) editor

render :: forall aff. State -> ParentHTML Query AceQuery Slot (Aff (AceEffects aff))
render state =
  div [ class_ (ClassName "main-frame") ] $
    [ container
      [ h1_ [ text "Plutus Playground" ]
      , hr_
      , slot AceComponent
          (aceComponent initEditor Nothing)
          unit
          (input HandleAceOutput)
      , hr_
      , h3_ [ text "Scaffolding"
            , text " "
            , small_ [ text "(ignore below this line)" ]
            ]
      , button
          [ classes
            [ if state.on
                 then btnPrimary
                 else btnSecondary
            ]
          , onClick $ input_ ToggleState
          ]
          [ text
              if not state.on
              then "Off"
              else "On"
          ]
      ]
    ]
