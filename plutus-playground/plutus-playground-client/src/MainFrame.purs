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
import Data.Either.Nested (Either2)
import Data.Functor.Coproduct.Nested (Coproduct2)
import Data.Lens (Lens', modifying)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested ((/\))
import Debug.Trace
import ECharts.Commands as E
import ECharts.Monad (DSL)
import ECharts.Types.Phantom as ETP
import Halogen (Component)
import Halogen as H
import Halogen.Component (ParentHTML)
import Halogen.Component.ChildPath (ChildPath, cp1, cp2)
import Halogen.ECharts (EChartsEffects, EChartsMessage, EChartsQuery, echarts)
import Halogen.ECharts as EC
import Halogen.HTML (ClassName(ClassName), HTML, button, div, h1_, h3_, hr_, slot', small_, text)
import Halogen.HTML.Events (input, input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Halogen.Query (HalogenM)
import Prelude (class Eq, class Ord, type (~>), Unit, Void, bind, const, discard, not, pure, unit, void, ($))

data Query a
  = ToggleState a
  | HandleAceMessage AceMessage a
  | HandleEChartsMessage EChartsMessage a

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

type ChildQuery = Coproduct2 AceQuery EChartsQuery
type ChildSlot = Either2 AceSlot EChartsSlot

data AceSlot = AceSlot
derive instance eqComponentAceSlot :: Eq AceSlot
derive instance ordComponentAceSlot :: Ord AceSlot

data EChartsSlot = EChartsSlot
derive instance eqComponentEChartsSlot :: Eq EChartsSlot
derive instance ordComponentEChartsSlot :: Ord EChartsSlot

cpAce :: ChildPath AceQuery ChildQuery AceSlot ChildSlot
cpAce = cp1

cpECharts :: ChildPath EChartsQuery ChildQuery EChartsSlot ChildSlot
cpECharts = cp2

------------------------------------------------------------

mainFrame :: forall aff. Component HTML Query Unit Void (Aff (EChartsEffects (AceEffects aff)))
mainFrame =
  H.parentComponent
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }

eval :: forall m. Query ~> HalogenM State Query ChildQuery ChildSlot Void m
eval (ToggleState next) = do
  modifying _on not
  pure next

eval (HandleAceMessage (TextChanged msg) next) = do
  void $ traceAnyM msg
  pure next

eval (HandleEChartsMessage EC.Initialized next) = do
  _ <- H.query' cp2 EChartsSlot $ H.action $ EC.Set sankeyDiagramOptions
  pure next

------------------------------------------------------------
initEditor ∷ forall aff. Editor -> Aff (ace :: ACE | aff) Unit
initEditor editor = liftEff $ do
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session
  void $ Editor.setValue initialText (Just 1) editor

render :: forall aff. State -> ParentHTML Query ChildQuery ChildSlot (Aff (EChartsEffects (AceEffects aff)))
render state =
  div [ class_ (ClassName "main-frame") ] $
    [ container
      [ h1_ [ text "Plutus Playground" ]
      , hr_
      , slot' cpAce AceSlot
          (aceComponent initEditor Nothing)
          unit
          (input HandleAceMessage)
      , hr_
      , slot' cpECharts EChartsSlot
          (echarts Nothing)
          ({width: 800, height: 400} /\ unit)
          (input HandleEChartsMessage)
      ]
      , scaffold state
    ]

scaffold :: forall p. State -> HTML p (Query Unit)
scaffold state =
  div [ class_ (ClassName "scaffold") ] $
    [ hr_
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

sankeyDiagramOptions :: DSL ETP.OptionI
sankeyDiagramOptions = do
  E.series $ E.sankey do
    E.buildItems do
      E.addItem do
        E.name "charles"
        E.value 600.0
      E.addItem do
        E.name "kris"
        E.value 10.0
      E.addItem do
        E.name "david"
        E.value 15.0
      E.addItem do
        E.name "manuel"
        E.value 123.0
    E.buildLinks do
      E.addLink do
        E.sourceName "charles"
        E.targetName "kris"
        E.value 10.0
      E.addLink do
        E.sourceName "charles"
        E.targetName "david"
        E.value 10.0
      E.addLink do
        E.sourceName "charles"
        E.targetName "manuel"
        E.value 20.0
