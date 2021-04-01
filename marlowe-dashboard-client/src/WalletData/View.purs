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
import Halogen.HTML (HTML, button, datalist, div, h2, h3, input, label, li, option, p, p_, text, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, id_, placeholder, readOnly, type_, value)
import Material.Icons (Icon(..))
import Play.Types (Action(..), Card(..))
import WalletData.Lenses (_contractInstanceId, _contractInstanceIdString, _remoteDataPubKey, _remoteDataValue, _remoteDataWallet, _walletNickname, _walletNicknameString)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletLibrary)
import WalletData.Validation (contractInstanceIdError, walletNicknameError)

newWalletCard :: forall p. WalletLibrary -> NewWalletDetails -> Maybe String -> HTML p Action
newWalletCard library newWalletDetails mTokenName =
  let
    walletNicknameString = view _walletNicknameString newWalletDetails

    contractInstanceIdString = view _contractInstanceIdString newWalletDetails

    remoteDataWallet = view _remoteDataWallet newWalletDetails

    remoteDataPubKey = view _remoteDataPubKey newWalletDetails

    remoteDataValue = view _remoteDataValue newWalletDetails

    mWalletNicknameError = walletNicknameError walletNicknameString library

    mContractInstanceIdError = contractInstanceIdError contractInstanceIdString remoteDataWallet remoteDataPubKey remoteDataValue library
  in
    div
      [ classNames [ "flex", "flex-col", "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Create new contact" <> foldMap (\tokenName -> " for role " <> show tokenName) mTokenName ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null walletNicknameString) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null walletNicknameString) ]
              [ text "Nickname" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mWalletNicknameError
              , placeholder "Nickname"
              , value walletNicknameString
              , onValueInput_ SetNewWalletNickname
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mWalletNicknameError ]
          ]
      , div
          [ classNames $ [ "mb-4" ] <> (applyWhen (not null contractInstanceIdString) Css.hasNestedLabel) ]
          [ label
              [ classNames $ Css.nestedLabel <> hideWhen (null contractInstanceIdString) ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input $ isJust mContractInstanceIdError
              , placeholder "Wallet ID"
              , value contractInstanceIdString
              , onValueInput_ SetNewWalletContractId
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mContractInstanceIdError ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mWalletNicknameError || isJust mContractInstanceIdError
              , onClick_ $ AddNewWallet mTokenName
              ]
              [ text "Save" ]
          ]
      ]

walletDetailsCard :: forall p a. WalletDetails -> HTML p a
walletDetailsCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    contractInstanceId = view _contractInstanceId walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ h3
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Wallet " <> walletNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-4" ]
              , value "" -- TODO: convert contractInstanceId to string
              , readOnly true
              ]
          ]
      ]

putdownWalletCard :: forall p. WalletDetails -> HTML p Action
putdownWalletCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    contractInstanceId = view _contractInstanceId walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ h3
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text $ "Wallet " <> walletNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false <> [ "mb-4" ]
              , value "" -- TODO: convert contractInstanceId to string
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
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
  div
    [ classNames [ "p-4", "md:px-5pc" ] ]
    [ h2
        [ classNames [ "font-semibold", "text-lg", "mb-4" ] ]
        [ text "Contacts" ]
    , if isEmpty library then
        p_ [ text "You do not have any contacts." ]
      else
        ul_
          $ contactLi
          <$> toUnfoldable library
    , button
        [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
        , onClick_ $ ToggleCard $ CreateWalletCard Nothing
        ]
        [ text "New contact" ]
    ]
  where
  contactLi (Tuple nickname walletDetails) =
    let
      contractId = view _contractInstanceId walletDetails
    in
      li
        [ classNames [ "mt-4", "hover:cursor-pointer", "hover:text-green" ]
        , onClick_ $ ToggleCard $ ViewWalletCard walletDetails
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
