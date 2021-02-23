module WalletData.View
  ( pickupWalletScreen
  , pickupNewWalletCard
  , pickupLocalWalletCard
  , putdownWalletCard
  , walletLibraryScreen
  , newContactCard
  , contactDetailsCard
  ) where

import Prelude hiding (div)
import Css (classNames, toggleWhen)
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..), fst, snd)
import Halogen.HTML (HTML, a, br_, button, datalist, div, footer, h2_, header, hr_, input, label, li, main, option, p, p_, span, text, ul)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, type_, value)
import MainFrame.Types (Action(..), Card(..))
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import WalletData.Lenses (_key, _nickname)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNicknameKey)
import WalletData.Validation (keyError, nicknameError)

pickupWalletScreen :: forall p. WalletLibrary -> HTML p Action
pickupWalletScreen wallets =
  div
    [ classNames [ "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link Icon.navigateBefore "Back to marlowe.io" "" ]
    , main
        [ classNames [ "flex", "flex-col", "p-1", "max-w-md", "mx-auto" ] ]
        [ h2_
            [ text "Welcome to the Marlowe Dashboard" ]
        , p
            [ classNames [ "mb-1" ] ]
            [ text "Here be some words of wisdom." ]
        , button
            [ classNames [ "mb-1" ]
            , onClick $ const $ Just GenerateNewWallet
            ]
            [ text "Generate play wallet" ]
        , label
            [ classNames [ "text-sm", "font-bold" ]
            , for "existingWallet"
            ]
            [ text "Pickup existing wallet" ]
        , input
            [ type_ InputText
            , id_ "existingWallet"
            , list "existingNicknames"
            , onValueInput $ Just <<< LookupWallet
            ]
        , datalist
            [ id_ "existingNicknames" ]
            $ walletOption
            <$> toUnfoldable wallets
        ]
    , footer
        [ classNames [ "flex" ] ]
        [ link Icon.navigateNext "Docs" ""
        , link Icon.navigateNext "Library" ""
        ]
    ]
  where
  link icon label url =
    a
      [ classNames [ "flex", "items-center", "text-green", "p-0.5" ]
      , href url
      ]
      [ icon, text label ]

  walletOption (Tuple (Tuple nickname _) _) = option [ value nickname ] []

pickupNewWalletCard :: forall p. WalletNicknameKey -> WalletLibrary -> HTML p Action
pickupNewWalletCard newWalletNicknameKey wallets =
  let
    nickname = view _nickname newWalletNicknameKey

    key = view _key newWalletNicknameKey

    mNicknameError = nicknameError nickname wallets
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2_
          [ text "New wallet generated" ]
      , label
          [ for "newWalletKey" ]
          [ text "Key:" ]
      , input
          [ type_ InputText
          , id_ "newWalletKey"
          , value key
          , readOnly true
          ]
      , br_
      , label
          [ for "newWalletNickname" ]
          [ text "Nickname:" ]
      , input
          [ type_ InputText
          , classNames $ toggleWhen (mNicknameError == Nothing) "border-green" "border-red"
          , id_ "newWalletNickname"
          , placeholder "Nickname"
          , value nickname
          , onValueInput $ Just <<< SetNewWalletNickname
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mNicknameError of
              Just nicknameError -> [ text $ show nicknameError ]
              Nothing -> []
      , button
          [ disabled $ isJust mNicknameError
          , onClick $ const $ Just PickupNewWallet
          ]
          [ text "Pickup new wallet" ]
      ]

pickupLocalWalletCard :: forall p. WalletNicknameKey -> HTML p Action
pickupLocalWalletCard walletNicknameKey =
  div
    [ classNames [ "flex", "flex-col" ] ]
    [ h2_
        [ text "Wallet found" ]
    , label
        [ for "newWalletKey" ]
        [ text "Key:" ]
    , input
        [ type_ InputText
        , id_ "newWalletKey"
        , value $ snd walletNicknameKey
        , readOnly true
        ]
    , br_
    , label
        [ for "newWalletNickname" ]
        [ text "Nickname:" ]
    , input
        [ type_ InputText
        , id_ "newWalletNickname"
        , placeholder "Nickname"
        , value $ fst walletNicknameKey
        , readOnly true
        ]
    , br_
    , button
        [ onClick $ const $ Just $ PickupWallet $ snd walletNicknameKey ]
        [ text "Pickup wallet" ]
    ]

putdownWalletCard :: forall p. PubKey -> WalletLibrary -> HTML p Action
putdownWalletCard pubKeyHash wallets =
  let
    mKey = findIndex (\key -> snd key == pubKeyHash) wallets

    mNickname = map fst mKey

    showNickname = case mNickname of
      Just nickname -> ": " <> show nickname
      Nothing -> ""
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2_
          [ text $ "Wallet" <> showNickname ]
      , input
          [ type_ InputText
          , classNames [ "mb-1" ]
          , value pubKeyHash
          , readOnly true
          ]
      , button
          [ onClick $ const $ Just PutdownWallet ]
          [ text "Put down wallet" ]
      ]

walletLibraryScreen :: forall p. WalletLibrary -> HTML p Action
walletLibraryScreen wallets =
  div
    [ classNames [ "p-1" ] ]
    [ h2_
        [ text "Contacts" ]
    , hr_
    , if isEmpty wallets then
        p_ [ text "You do not have any contacts." ]
      else
        ul
          [ classNames [ "mt-1" ] ]
          $ contactLi
          <$> toUnfoldable wallets
    , div
        [ classNames [ "absolute", "bottom-1", "left-1", "right-1" ] ]
        [ button
            [ classNames [ "w-full", "px-1", "flex", "justify-between", "items-center" ]
            , onClick $ const $ Just $ ToggleCard CreateWalletCard
            ]
            [ span
                [ classNames [ "mr-0.5" ] ]
                [ text "Create new contact" ]
            , Icon.personAdd
            ]
        ]
    ]
  where
  contactLi (Tuple localWalletKey@(Tuple nickname key) localWallet) =
    li
      [ classNames [ "mt-1", "hover:cursor-pointer", "hover:text-green" ]
      , onClick $ const $ Just $ ToggleCard $ ViewWalletCard localWalletKey localWallet
      ]
      [ text nickname ]

newContactCard :: forall p. WalletNicknameKey -> WalletLibrary -> HTML p Action
newContactCard newWalletNicknameKey wallets =
  let
    nickname = view _nickname newWalletNicknameKey

    key = view _key newWalletNicknameKey

    mNicknameError = nicknameError nickname wallets

    mKeyError = keyError key wallets
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2_
          [ text "Create new contact" ]
      , input
          [ type_ InputText
          , classNames $ toggleWhen (mNicknameError == Nothing) "border-green" "border-red"
          , placeholder "Nickname"
          , value nickname
          , onValueInput $ Just <<< SetNewWalletNickname
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mNicknameError of
              Just nicknameError -> [ text $ show nicknameError ]
              Nothing -> []
      , input
          [ type_ InputText
          , classNames $ toggleWhen (mKeyError == Nothing) "border-green" "border-red"
          , placeholder "Wallet key"
          , value key
          , onValueInput $ Just <<< SetNewWalletKey
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mKeyError of
              Just keyError -> [ text $ show keyError ]
              Nothing -> []
      , button
          [ disabled $ isJust mKeyError || isJust mNicknameError
          , onClick $ const $ Just AddNewWallet
          ]
          [ text "Save new contact" ]
      ]

contactDetailsCard :: forall p. WalletNicknameKey -> WalletDetails -> HTML p Action
contactDetailsCard walletNicknameKey walletDetails =
  div
    [ classNames [ "flex", "flex-col" ] ]
    [ h2_
        [ text "Contact details" ]
    , p_ [ text $ "Nickname: " <> view _nickname walletNicknameKey ]
    , p_ [ text $ "Wallet key: " <> view _key walletNicknameKey ]
    ]
