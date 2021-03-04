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
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Map (isEmpty, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.String (null)
import Data.Tuple (Tuple(..))
import Halogen.HTML (HTML, button, datalist, div, div_, h2, h3, input, label, li, option, p, p_, span, text, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, id_, placeholder, readOnly, type_, value)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Network.RemoteData (RemoteData)
import Play.Types (Action(..), Card(..))
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Lenses (_contractId, _nickname)
import WalletData.Types (Nickname, WalletDetails, WalletLibrary)
import WalletData.Validation (contractIdError, nicknameError)

newWalletCard :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> HTML p Action
newWalletCard library newWalletDetails newWalletPubKey =
  let
    nickname = view _nickname newWalletDetails

    contractId = view _contractId newWalletDetails

    mNicknameError = nicknameError nickname library

    mContractIdError = contractIdError contractId newWalletPubKey library
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ p
          [ classNames [ "mb-1" ] ]
          [ text "Create new contact" ]
      , div
          [ classNames $ [ "mb-1" ] <> (applyWhen (not null nickname) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null nickname) ]
              [ text "Nickname" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mNicknameError
              , placeholder "Nickname"
              , value nickname
              , onValueInput_ SetNewWalletNickname
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mNicknameError ]
          ]
      , div
          [ classNames $ [ "mb-1" ] <> (applyWhen (not null contractId) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null contractId) ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mContractIdError
              , placeholder "Wallet ID"
              , value contractId
              , onValueInput_ SetNewWalletContractId
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mContractIdError ]
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
              , disabled $ isJust mNicknameError || isJust mContractIdError
              , onClick_ AddNewWallet
              ]
              [ text "Save" ]
          ]
      ]

walletDetailsCard :: forall p a. Nickname -> String -> HTML p a
walletDetailsCard nickname contractId =
  div_
    [ h3
        [ classNames [ "font-bold", "mb-1" ] ]
        [ text $ "Wallet " <> nickname ]
    , div
        [ classNames Css.hasNestedLabel ]
        [ label
            [ classNames Css.nestedLabel ]
            [ text "Wallet ID" ]
        , input
            [ type_ InputText
            , classNames $ Css.input false <> [ "mb-1" ]
            , value contractId
            , readOnly true
            ]
        ]
    ]

putdownWalletCard :: forall p. WalletDetails -> HTML p Action
putdownWalletCard walletDetails =
  div_
    [ h3
        [ classNames [ "font-bold", "mb-1" ] ]
        [ text $ "Wallet " <> view _nickname walletDetails ]
    , div
        [ classNames Css.hasNestedLabel ]
        [ label
            [ classNames Css.nestedLabel ]
            [ text "Wallet ID" ]
        , input
            [ type_ InputText
            , classNames $ Css.input false <> [ "mb-1" ]
            , value $ view _contractId walletDetails
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
walletLibraryScreen library =
  div_
    [ h2
        [ classNames [ "font-bold", "mb-1" ] ]
        [ text "Contacts" ]
    , if isEmpty library then
        p_ [ text "You do not have any contacts." ]
      else
        ul_
          $ contactLi
          <$> toUnfoldable library
    , button
        [ classNames Css.fixedPrimaryButton
        , onClick_ $ ToggleCard CreateWalletCard
        ]
        [ span
            [ classNames [ "mr-0.5" ] ]
            [ text "New contact" ]
        , Icon.add
        ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    let
      contractId = view _contractId walletDetails
    in
      li
        [ classNames [ "mt-1", "hover:cursor-pointer", "hover:text-green" ]
        , onClick_ $ ToggleCard $ ViewWalletCard nickname contractId
        ]
        [ text nickname ]

nicknamesDataList :: forall p a. WalletLibrary -> HTML p a
nicknamesDataList library =
  datalist
    [ id_ "walletNicknames" ]
    $ walletOption
    <$> toUnfoldable library
  where
  walletOption (Tuple nickname _) = option [ value nickname ] []
