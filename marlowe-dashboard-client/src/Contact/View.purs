module Contact.View
  ( renderContacts
  , renderNewContact
  , renderContact
  ) where

import Prelude hiding (div)
import Contact.Types (Action(..), Contact, ContactKey)
import Contact.Validation (keyError, nicknameError)
import Css (buttonClasses, classNames, h2Classes, textInputClasses, toggleWhen)
import Data.Lens (view)
import Data.Lens.Lens.Tuple (_1, _2)
import Data.Map (Map, isEmpty, lookup, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..))
import Halogen.HTML (HTML, button, div, h2, hr_, input, li, p_, span, text, ul)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (InputType(..), disabled, placeholder, type_, value)
import Material.Icons as Icon

renderContacts :: forall p. Map ContactKey Contact -> HTML p Action
renderContacts contacts =
  div
    [ classNames [ "p-1" ] ]
    [ h2
        [ classNames h2Classes ]
        [ text "Contacts" ]
    , hr_
    , if isEmpty contacts then
        p_ [ text "You do not have any contacts." ]
      else
        ul
          [ classNames [ "mt-1" ] ]
          $ contactLi
          <$> toUnfoldable contacts
    , div
        [ classNames [ "absolute", "bottom-1", "left-1", "right-1" ] ]
        [ button
            [ classNames $ buttonClasses <> [ "w-full", "px-1", "flex", "justify-between", "items-center", "bg-green", "text-white" ]
            , onClick $ const $ Just $ ToggleNewContactCard
            ]
            [ span
                [ classNames [ "mr-0.5" ] ]
                [ text "Create new contact" ]
            , Icon.personAdd
            ]
        ]
    ]
  where
  contactLi (Tuple contactKey@(Tuple nickname key) contact) =
    li
      [ classNames [ "mt-1", "hover:cursor-pointer", "hover:text-green" ]
      , onClick $ const $ Just $ ToggleEditContactCard contactKey
      ]
      [ text nickname ]

renderNewContact :: forall p. ContactKey -> Map ContactKey Contact -> HTML p Action
renderNewContact newContactKey contacts =
  let
    nickname = view _1 newContactKey

    key = view _2 newContactKey

    mNicknameError = nicknameError nickname contacts

    mKeyError = keyError key contacts
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2
          [ classNames h2Classes ]
          [ text "Create new contact" ]
      , input
          [ type_ InputText
          , classNames $ textInputClasses <> toggleWhen (mNicknameError == Nothing) "border-green" "border-red"
          , placeholder "Nickname"
          , value nickname
          , onValueInput $ Just <<< SetNewContactNickname
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mNicknameError of
              Just nicknameError -> [ text $ show nicknameError ]
              Nothing -> []
      , input
          [ type_ InputText
          , classNames $ textInputClasses <> toggleWhen (mKeyError == Nothing) "border-green" "border-red"
          , placeholder "Wallet key"
          , value key
          , onValueInput $ Just <<< SetNewContactKey
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mKeyError of
              Just keyError -> [ text $ show keyError ]
              Nothing -> []
      , button
          [ classNames $ buttonClasses <> [ "bg-green", "text-white" ]
          , disabled $ isJust mKeyError || isJust mNicknameError
          , onClick $ const $ Just AddNewContact
          ]
          [ text "Save new contact" ]
      ]

renderContact :: forall p. ContactKey -> Map ContactKey Contact -> HTML p Action
renderContact contactKey contacts = case lookup contactKey contacts of
  Just contact ->
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2
          [ classNames h2Classes ]
          [ text "Contact details" ]
      , p_ [ text $ "Nickname: " <> view _1 contactKey ]
      , p_ [ text $ "Wallet key: " <> view _2 contactKey ]
      ]
  Nothing -> div [] []
