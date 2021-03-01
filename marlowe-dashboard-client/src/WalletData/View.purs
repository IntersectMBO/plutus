module WalletData.View
  ( newWalletCard
  , walletDetailsCard
  , putdownWalletCard
  , walletLibraryScreen
  , nicknamesDataList
  ) where

import Prelude hiding (div)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Map.Extra (findIndex)
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..), fst, snd)
import Halogen.HTML (HTML, button, datalist, div, div_, h2, h3, input, label, li, option, p, p_, span, text, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
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
      [ p
          [ classNames [ "mb-1" ] ]
          [ text "Create new contact" ]
      , div
          [ classNames $ [ "mb-1" ] <> (applyWhen (nickname /= "") Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (nickname == "") ]
              [ text "Nickname:" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mNicknameError
              , placeholder "Nickname"
              , value nickname
              , onValueInput_ SetNewWalletNickname
              ]
          , div
              [ classNames Css.inputError ]
              $ case mNicknameError of
                  Just nicknameError -> [ text $ show nicknameError ]
                  Nothing -> []
          ]
      , div
          [ classNames $ [ "mb-1" ] <> (applyWhen (key /= "") Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (key == "") ]
              [ text "Public key:" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mKeyError
              , placeholder "Public key"
              , value key
              , onValueInput_ SetNewWalletKey
              ]
          , div
              [ classNames Css.inputError ]
              $ case mKeyError of
                  Just keyError -> [ text $ show keyError ]
                  Nothing -> []
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-1" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mKeyError || isJust mNicknameError
              , onClick_ AddNewWallet
              ]
              [ text "Save" ]
          ]
      ]

walletDetailsCard :: forall p a. WalletNicknameKey -> WalletDetails -> HTML p a
walletDetailsCard walletNicknameKey walletDetails =
  let
    nickname = view _nickname walletNicknameKey

    key = view _key walletNicknameKey
  in
    div_
      [ h3
          [ classNames [ "font-bold", "mb-1" ] ]
          [ text $ "Wallet " <> nickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Public key" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-1" ]
              , value key
              , readOnly true
              ]
          ]
      ]

putdownWalletCard :: forall p. PubKey -> WalletLibrary -> HTML p Action
putdownWalletCard pubKeyHash wallets =
  let
    mKey = findIndex (\key -> snd key == pubKeyHash) wallets

    mNickname = map fst mKey

    showNickname = case mNickname of
      Just nickname -> " " <> nickname
      Nothing -> ""
  in
    div_
      [ h3
          [ classNames [ "font-bold", "mb-1" ] ]
          [ text $ "Wallet" <> showNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Public key" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-1" ]
              , value pubKeyHash
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-1" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ PutdownWallet
              ]
              [ text "Drop wallet" ]
          ]
      ]

walletLibraryScreen :: forall p. WalletLibrary -> HTML p Action
walletLibraryScreen wallets =
  div_
    [ h2
        [ classNames [ "font-bold", "mb-1" ] ]
        [ text "Contacts" ]
    , if isEmpty wallets then
        p_ [ text "You do not have any contacts." ]
      else
        ul_
          $ contactLi
          <$> toUnfoldable wallets
    , button
        [ classNames Css.fixedPrimaryButton
        , onClick_ $ ToggleCard CreateWalletCard
        ]
        [ span
            [ classNames [ "mr-0.5" ] ]
            [ text "New contact" ]
        , Icon.personAdd
        ]
    ]
  where
  contactLi (Tuple localWalletKey@(Tuple nickname key) localWallet) =
    li
      [ classNames [ "mt-1", "hover:cursor-pointer", "hover:text-green" ]
      , onClick_ $ ToggleCard $ ViewWalletCard localWalletKey localWallet
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
