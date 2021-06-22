module MetadataTab.View (metadataView) where

import Prelude hiding (div)
import Data.Array (concat, concatMap)
import Data.Lens (Lens', (^.))
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set, toUnfoldable)
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.Classes (minusBtn, plusBtn, smallBtn, btn)
import Halogen.HTML (ClassName(..), HTML, button, div, em_, h6_, input, option, select, text)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, placeholder, selected, type_, value)
import Marlowe.Extended (contractTypeArray, contractTypeInitials, contractTypeName, initialsToContractType)
import Marlowe.Extended.Metadata (ChoiceInfo, MetaData, MetadataHintInfo, _choiceDescription, _choiceInfo, _choiceNames, _roleDescriptions, _roles, _slotParameterDescriptions, _slotParameters, _valueParameterDescriptions, _valueParameters)
import MetadataTab.Types (MetadataAction(..))

onlyDescriptionRenderer :: forall a b p. (String -> String -> b) -> (String -> b) -> String -> String -> Boolean -> (b -> a) -> String -> String -> Array (HTML p a)
onlyDescriptionRenderer setAction deleteAction key info needed metadataAction typeNameTitle typeNameSmall =
  [ div [ class_ $ ClassName "metadata-prop-label" ]
      [ text $ typeNameTitle <> " " <> show key <> ": " ]
  , div [ class_ $ ClassName "metadata-prop-edit" ]
      [ input
          [ type_ InputText
          , placeholder $ "Description for " <> typeNameSmall <> " " <> show key
          , class_ $ ClassName "metadata-input"
          , value info
          , onValueChange $ Just <<< metadataAction <<< setAction key
          ]
      ]
  , div [ class_ $ ClassName "metadata-prop-delete" ]
      [ button
          [ classes [ if needed then plusBtn else minusBtn, smallBtn, ClassName "align-top", btn ]
          , onClick $ const $ Just $ metadataAction $ deleteAction key
          ]
          [ text "-" ]
      ]
  ]
    <> if needed then [] else [ div [ classes [ ClassName "metadata-error", ClassName "metadata-prop-not-used" ] ] [ text "Not used" ] ]

choiceMetadataRenderer :: forall a p. String -> ChoiceInfo -> Boolean -> (MetadataAction -> a) -> String -> String -> Array (HTML p a)
choiceMetadataRenderer key info needed metadataAction typeNameTitle typeNameSmall =
  [ div [ class_ $ ClassName "metadata-prop-label" ]
      [ text $ typeNameTitle <> " " <> show key <> ": " ]
  , div [ class_ $ ClassName "metadata-prop-edit" ]
      [ input
          [ type_ InputText
          , placeholder $ "Description for " <> typeNameSmall <> " " <> show key
          , class_ $ ClassName "metadata-input"
          , value (info ^. _choiceDescription)
          , onValueChange $ Just <<< metadataAction <<< SetChoiceDescription key
          ]
      ]
  , div [ class_ $ ClassName "metadata-prop-delete" ]
      [ button
          [ classes [ if needed then plusBtn else minusBtn, smallBtn, ClassName "align-top", btn ]
          , onClick $ const $ Just $ metadataAction $ DeleteChoiceInfo key
          ]
          [ text "-" ]
      ]
  ]
    <> if needed then [] else [ div [ classes [ ClassName "metadata-error", ClassName "metadata-prop-not-used" ] ] [ text "Not used" ] ]

metadataList ::
  forall a b c p.
  (b -> a) ->
  Map String c ->
  Set String ->
  (String -> c -> Boolean -> (b -> a) -> String -> String -> Array (HTML p a)) ->
  String -> String -> (String -> b) -> Array (HTML p a)
metadataList metadataAction metadataMap hintSet metadataRenderer typeNameTitle typeNameSmall setEmptyMetadata =
  if Map.isEmpty combinedMap then
    []
  else
    [ div [ class_ $ ClassName "metadata-group-title" ]
        [ h6_ [ em_ [ text $ typeNameTitle <> " descriptions" ] ] ]
    ]
      <> ( concatMap
            ( \(key /\ val) ->
                ( case val of
                    Just (info /\ needed) -> metadataRenderer key info needed metadataAction typeNameTitle typeNameSmall
                    Nothing ->
                      [ div [ classes [ ClassName "metadata-error", ClassName "metadata-prop-not-defined" ] ]
                          [ text $ typeNameTitle <> " " <> show key <> " meta-data not defined" ]
                      , div [ class_ $ ClassName "metadata-prop-create" ]
                          [ button
                              [ classes [ minusBtn, smallBtn, ClassName "align-top", btn ]
                              , onClick $ const $ Just $ metadataAction (setEmptyMetadata key)
                              ]
                              [ text "+" ]
                          ]
                      ]
                )
            )
            $ Map.toUnfoldable combinedMap
        )
  where
  mergeMaps :: forall c2. (Maybe (c2 /\ Boolean)) -> (Maybe (c2 /\ Boolean)) -> (Maybe (c2 /\ Boolean))
  mergeMaps (Just (x /\ _)) _ = Just (x /\ true)

  mergeMaps _ _ = Nothing

  -- The value of the Map has the following meaning:
  -- * Nothing means the entry is in the contract but not in the metadata
  -- * Just (_ /\ false) means the entry is in the metadata but not in the contract
  -- * Just (_ /\ true) means the entry is both in the contract and in the metadata
  -- If it is nowhere we just don't store it in the map
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
        , generateMetadataList _roleDescriptions _roles (onlyDescriptionRenderer SetRoleDescription DeleteRoleDescription) "Role" "role" (\x -> SetRoleDescription x mempty)
        , generateMetadataList _choiceInfo _choiceNames choiceMetadataRenderer "Choice" "choice" (\x -> SetChoiceDescription x mempty)
        , generateMetadataList _slotParameterDescriptions _slotParameters (onlyDescriptionRenderer SetSlotParameterDescription DeleteSlotParameterDescription) "Slot parameter" "slot parameter" (\x -> SetSlotParameterDescription x mempty)
        , generateMetadataList _valueParameterDescriptions _valueParameters (onlyDescriptionRenderer SetValueParameterDescription DeleteValueParameterDescription) "Value parameter" "value parameter" (\x -> SetValueParameterDescription x mempty)
        ]
    )
  where
  generateMetadataList ::
    forall c.
    Lens' MetaData (Map String c) ->
    Lens' MetadataHintInfo (Set String) ->
    (String -> c -> Boolean -> (MetadataAction -> a) -> String -> String -> Array (HTML p a)) ->
    String ->
    String ->
    (String -> MetadataAction) ->
    Array (HTML p a)
  generateMetadataList mapLens setLens = metadataList metadataAction (metadata ^. mapLens) (metadataHints ^. setLens)
