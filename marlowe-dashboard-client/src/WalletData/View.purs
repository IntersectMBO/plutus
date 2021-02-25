module WalletData.View
  ( newWalletCard
  , walletDetailsCard
  , putdownWalletCard
  , walletLibraryScreen
  , nicknamesDataList
  ) where

import Prelude hiding (div)
import Css (classNames, toggleWhen)
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..), fst, snd)
import Halogen.HTML (HTML, button, datalist, div, div_, h2_, hr_, input, li, option, p_, span, text, ul)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (InputType(..), disabled, id_, placeholder, readOnly, type_, value)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Play.Types (Action(..), Card(..))
import WalletData.Lenses (_key, _nickname)
import WalletData.Types (WalletDetails, WalletLibrary, WalletNicknameKey)
import WalletData.Validation (keyError, nicknameError)

newWalletCard :: forall p. WalletNicknameKey -> WalletLibrary -> HTML p Action
newWalletCard newWalletNicknameKey wallets =
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

walletDetailsCard :: forall p a. WalletNicknameKey -> WalletDetails -> HTML p a
walletDetailsCard walletNicknameKey walletDetails =
  div
    [ classNames [ "flex", "flex-col" ] ]
    [ h2_
        [ text "Contact details" ]
    , p_ [ text $ "Nickname: " <> view _nickname walletNicknameKey ]
    , p_ [ text $ "Wallet key: " <> view _key walletNicknameKey ]
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
  div_
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

nicknamesDataList :: forall p a. WalletLibrary -> HTML p a
nicknamesDataList wallets =
  datalist
    [ id_ "walletNicknames" ]
    $ walletOption
    <$> toUnfoldable wallets
  where
  walletOption (Tuple (Tuple nickname _) _) = option [ value nickname ] []
