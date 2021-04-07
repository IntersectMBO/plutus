module BottomPanel.View (render, metadataView) where

import Prelude hiding (div)
import BottomPanel.Types (Action(..), MetadataAction(..), State, _panelView, _showBottomPanel)
import Data.Array (concat, concatMap)
import Data.Lens (to, (^.))
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set, toUnfoldable)
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.Classes (accentBorderTop, borderSeparator, boxShadowInverted, closeDrawerArrowIcon, collapsed, flex, flexCol, flexShrink0, fontBold, fullHeight, hidden, justifyBetween, minH0, minimizeIcon, minusBtn, paddingX, plusBtn, scroll, smallBtn, smallPaddingRight, smallPaddingTop, smallPaddingY, spaceX, textInactive, textSecondary)
import Halogen.HTML (ClassName(..), HTML, a, button, div, em_, h6_, img, input, option, select, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, placeholder, selected, src, type_, value)
import Marlowe.Extended (contractTypeArray, contractTypeInitials, contractTypeName, initialsToContractType)
import Marlowe.Extended.Metadata (MetadataHintInfo, MetaData, _choiceDescriptions, _choiceNames, _roleDescriptions, _roles, _slotParameterDescriptions, _slotParameters, _valueParameterDescriptions, _valueParameters)

type PanelTitle panel
  = { view :: panel
    , classes :: Array ClassName
    , title :: String
    }

render ::
  forall p panel action.
  -- The panel equality restriction allow us to identify the current selected panel.
  Eq panel =>
  -- panelTitles is an ordered list of the titles we'll show in the widget. The caller needs to provide a
  -- `title` name to display, the `view` that is selected when the title is clicked and a list
  -- of `classes` to optionally style the titles.
  Array (PanelTitle panel) ->
  -- The panelContent function receives the active panel and returns it's content. The `action` type parameter
  -- is what allow us to fire an action from the child that is intended to be interpreted on the parent.
  (panel -> HTML p (Action panel action)) ->
  State panel ->
  HTML p (Action panel action)
render panelTitles panelContent state =
  div [ classes ([ boxShadowInverted, flex, flexCol, fullHeight ] <> collapseWhenHidden) ]
    -- Header
    [ div [ classes [ flexShrink0, smallPaddingTop, flex, justifyBetween ] ]
        -- Titles
        [ div [ classes [ borderSeparator ] ]
            ( panelTitles
                <#> \panelTitle ->
                    a
                      [ classes ([ fontBold, paddingX ] <> panelTitle.classes <> activeClasses panelTitle.view)
                      , onClick $ clickTitleAction panelTitle.view
                      ]
                      [ text panelTitle.title ]
            )
        -- Visibility toggle
        , div [ classes [ smallPaddingRight ] ]
            [ a [ onClick $ const $ Just $ SetVisibility (state ^. _showBottomPanel <<< to not) ]
                [ img [ classes (minimizeIcon $ state ^. _showBottomPanel), src closeDrawerArrowIcon, alt "close drawer icon" ] ]
            ]
        ]
    -- Panel contents
    , div [ classes ([ spaceX, smallPaddingY, accentBorderTop, scroll, minH0 ] <> dontDisplayWhenHidden) ]
        [ panelContent (state ^. _panelView)
        ]
    ]
  where
  -- When the user clicks on a panel title header, if it's the current view it toggles the
  -- visibility, and if not it changes to that panel (which also shows the panel if hidden)
  clickTitleAction view =
    if state ^. _panelView == view then
      const $ Just $ SetVisibility (state ^. _showBottomPanel <<< to not)
    else
      const $ Just $ ChangePanel $ view

  activeClasses view = if state ^. _panelView == view then [ textSecondary ] else [ textInactive ]

  dontDisplayWhenHidden = if state ^. _showBottomPanel then [] else [ hidden ]

  collapseWhenHidden = if state ^. _showBottomPanel then [] else [ collapsed ]

metadataList :: forall a b p. (b -> a) -> Map String String -> Set String -> (String -> String -> b) -> (String -> b) -> String -> String -> Array (HTML p a)
metadataList metadataAction metadataMap hintSet setAction deleteAction typeNameTitle typeNameSmall =
  if Map.isEmpty combinedMap then
    []
  else
    [ div [ class_ $ ClassName "metadata-group-title" ]
        [ h6_ [ em_ [ text $ typeNameTitle <> " descriptions" ] ] ]
    ]
      <> ( concatMap
            ( \(key /\ val) ->
                ( case val of
                    Just (desc /\ needed) ->
                      [ div [ class_ $ ClassName "metadata-prop-label" ]
                          [ text $ typeNameTitle <> " " <> show key <> ": " ]
                      , div [ class_ $ ClassName "metadata-prop-edit" ]
                          [ input
                              [ type_ InputText
                              , placeholder $ "Description for " <> typeNameSmall <> " " <> show key
                              , class_ $ ClassName "metadata-input"
                              , value desc
                              , onValueChange $ Just <<< metadataAction <<< setAction key
                              ]
                          ]
                      , div [ class_ $ ClassName "metadata-prop-delete" ]
                          [ button
                              [ classes [ if needed then plusBtn else minusBtn, smallBtn, ClassName "align-top" ]
                              , onClick $ const $ Just $ metadataAction $ deleteAction key
                              ]
                              [ text "-" ]
                          ]
                      ]
                        <> if needed then [] else [ div [ classes [ ClassName "metadata-error", ClassName "metadata-prop-not-used" ] ] [ text "Not used" ] ]
                    Nothing ->
                      [ div [ classes [ ClassName "metadata-error", ClassName "metadata-prop-not-defined" ] ]
                          [ text $ typeNameTitle <> " " <> show key <> " description not defined" ]
                      , div [ class_ $ ClassName "metadata-prop-create" ]
                          [ button
                              [ classes [ minusBtn, smallBtn, ClassName "align-top" ]
                              , onClick $ const $ Just $ metadataAction $ setAction key mempty
                              ]
                              [ text "+" ]
                          ]
                      ]
                )
            )
            $ Map.toUnfoldable combinedMap
        )
  where
  mergeMaps :: (Maybe (String /\ Boolean)) -> (Maybe (String /\ Boolean)) -> (Maybe (String /\ Boolean))
  mergeMaps (Just (x /\ _)) _ = Just (x /\ true)

  mergeMaps _ _ = Nothing

  -- The value of the Map has the following meaning:
  -- * Nothing means the entry is in the contract but not in the metadata
  -- * Just (_ /\ false) means the entry is in the metadata but not in the contract
  -- * Just (_ /\ true) means the entry is both in the contract and in the metadata
  -- If it is nowhere we just don't store it in the map
  combinedMap :: Map String (Maybe (String /\ Boolean))
  combinedMap =
    Map.unionWith mergeMaps
      (map (\x -> Just (x /\ false)) metadataMap)
      (Map.fromFoldable (map (\x -> x /\ Nothing) ((toUnfoldable hintSet) :: List String)))

metadataView :: forall a p. MetadataHintInfo -> MetaData -> (MetadataAction -> a) -> HTML p a
metadataView metadataHints metadata metadataAction =
  div [ classes [ ClassName "metadata-form" ] ]
    ( concat
        [ [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract type: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ select
                  [ class_ $ ClassName "metadata-input"
                  , onValueChange $ Just <<< metadataAction <<< SetContractType <<< initialsToContractType
                  ] do
                  ct <- contractTypeArray
                  pure
                    $ option
                        [ value $ contractTypeInitials ct
                        , selected (ct == metadata.contractType)
                        ]
                        [ text $ contractTypeName ct
                        ]
              ]
          ]
        , [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract name: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ input
                  [ type_ InputText
                  , placeholder "Contract name"
                  , class_ $ ClassName "metadata-input"
                  , value metadata.contractName
                  , onValueChange $ Just <<< metadataAction <<< SetContractName
                  ]
              ]
          ]
        , [ div [ class_ $ ClassName "metadata-mainprop-label" ]
              [ text "Contract description: " ]
          , div [ class_ $ ClassName "metadata-mainprop-edit" ]
              [ input
                  [ type_ InputText
                  , placeholder "Contract description"
                  , class_ $ ClassName "metadata-input"
                  , value metadata.contractDescription
                  , onValueChange $ Just <<< metadataAction <<< SetContractDescription
                  ]
              ]
          ]
        , generateMetadataList _roleDescriptions _roles SetRoleDescription DeleteRoleDescription "Role" "role"
        , generateMetadataList _choiceDescriptions _choiceNames SetChoiceDescription DeleteChoiceDescription "Choice" "choice"
        , generateMetadataList _slotParameterDescriptions _slotParameters SetSlotParameterDescription DeleteSlotParameterDescription "Slot parameter" "slot parameter"
        , generateMetadataList _valueParameterDescriptions _valueParameters SetValueParameterDescription DeleteValueParameterDescription "Value parameter" "value parameter"
        ]
    )
  where
  generateMetadataList mapLens setLens = metadataList metadataAction (metadata ^. mapLens) (metadataHints ^. setLens)
