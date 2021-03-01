module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div, min)
import Css (applyWhen, classNames)
import Css as Css
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.Map (Map, lookup)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (toUnfoldable) as Set
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, button, div, div_, h2, h3, input, label, li, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, for, id_, list, min, placeholder, readOnly, type_, value)
import Marlowe.Extended (Contract, IntegerTemplateType(..), TemplateContent, _slotContent, _valueContent, getParties)
import Marlowe.Semantics (PubKey, Party(..))
import Material.Icons as Icon
import Template.Lenses (_contractNickname, _extendedContract, _metaData, _roleWallets, _template, _templateContent)
import Template.Types (Action(..), Screen(..), MetaData, State, Template)
import Template.Validation (roleError, roleWalletsAreValid, slotError, valueError)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList)

contractSetupScreen :: forall p. WalletLibrary -> Screen -> State -> HTML p Action
contractSetupScreen wallets setupScreen state =
  let
    contractNickname = view _contractNickname state

    metaData = view (_template <<< _metaData) state

    extendedContract = view (_template <<< _extendedContract) state

    roleWallets = view _roleWallets state

    templateContent = view _templateContent state
  in
    div
      []
      [ contractSetupScreenHeader setupScreen contractNickname
      , case setupScreen of
          ContractRolesScreen -> contractRolesScreen wallets metaData extendedContract roleWallets
          ContractParametersScreen -> contractParametersScreen metaData templateContent
          ContractReviewScreen -> contractReviewScreen state
      , div
          [ classNames [ "absolute", "bottom-1", "left-1", "right-1", "flex", "items-center", "justify-between" ] ]
          $ contractNavigationButtons setupScreen roleWallets wallets
      ]

contractSetupScreenHeader :: forall p. Screen -> String -> HTML p Action
contractSetupScreenHeader setupScreen contractNickname =
  div_
    [ div
        []
        [ input
            [ classNames [ "w-full", "text-center" ]
            , type_ InputText
            , placeholder "Contract name"
            , value contractNickname
            , onValueInput_ SetContractNickname
            ]
        ]
    , div
        [ classNames [ "flex", "justify-between" ] ]
        [ span
            [ classNames $ screenClasses setupScreen ContractRolesScreen ]
            [ text "Roles" ]
        , span
            [ classNames $ screenClasses setupScreen ContractParametersScreen ]
            [ text "Parameters" ]
        , span
            [ classNames $ screenClasses setupScreen ContractReviewScreen ]
            [ text "Review" ]
        ]
    ]
  where
  screenClasses currentScreen screen = [ "p-1" ] <> applyWhen (currentScreen == screen) [ "text-blue" ]

contractNavigationButtons :: forall p. Screen -> Map String String -> WalletLibrary -> Array (HTML p Action)
contractNavigationButtons screen roleWallets wallets = case screen of
  ContractRolesScreen ->
    [ a
        [ onClick_ ToggleTemplateLibraryCard ]
        [ text "< Library quick access" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ SetScreen ContractParametersScreen
        , enabled $ roleWalletsAreValid roleWallets wallets
        ]
        [ text "Next >" ]
    ]
  ContractParametersScreen ->
    [ a
        [ onClick_ $ SetScreen ContractRolesScreen ]
        [ text "< Roles" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ SetScreen ContractReviewScreen
        ]
        [ text "Next >" ]
    ]
  ContractReviewScreen ->
    [ a
        [ onClick_ $ SetScreen ContractParametersScreen ]
        [ text "< Parameters" ]
    , button
        [ classNames Css.primaryButton
        , onClick_ $ ToggleSetupConfirmationCard
        ]
        [ text "Pay and start >" ]
    ]

contractRolesScreen :: forall p. WalletLibrary -> MetaData -> Contract -> Map String PubKey -> HTML p Action
contractRolesScreen wallets metaData extendedContract roleWallets =
  ul
    [ classNames [ "mx-auto", "w-22" ] ]
    $ map partyInput (Set.toUnfoldable $ getParties extendedContract)
  where
  partyInput (PK pubKey) =
    li
      [ classNames [ "mb-1" ] ]
      [ label
          [ classNames [ "block", "mb-0.5" ]
          , for pubKey
          ]
          [ text "Wallet" ]
      , input
          [ classNames $ Css.input false
          , id_ pubKey
          , type_ InputText
          , value pubKey
          , readOnly true
          ]
      ]

  partyInput (Role tokenName) =
    let
      description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions

      assigned = fromMaybe "" $ lookup tokenName roleWallets

      mRoleError = roleError assigned wallets
    in
      li
        [ classNames [ "mb-1" ] ]
        [ label
            [ classNames [ "block", "mb-0.5" ]
            , for tokenName
            ]
            [ text $ tokenName <> ": " <> description ]
        , input
            [ classNames $ Css.input (isJust mRoleError)
            , id_ tokenName
            , type_ InputText
            , list "walletNicknames"
            , onValueInput_ $ SetRoleWallet tokenName
            , value assigned
            ]
        , div
            [ classNames Css.inputError ]
            $ case mRoleError of
                Just roleError -> [ text $ show roleError ]
                Nothing -> []
        , nicknamesDataList wallets
        ]

contractParametersScreen :: forall p. MetaData -> TemplateContent -> HTML p Action
contractParametersScreen metaData templateContent =
  let
    slotContent = view _slotContent templateContent

    valueContent = view _valueContent templateContent
  in
    div
      [ classNames [ "mx-auto", "w-22" ] ]
      [ ul
          [ classNames [ "mb-1" ] ]
          $ map (parameterInput SlotContent) (Map.toUnfoldable slotContent)
      , ul_
          $ map (parameterInput ValueContent) (Map.toUnfoldable valueContent)
      ]
  where
  parameterInput integerTemplateType (key /\ parameterValue) =
    let
      description = case integerTemplateType of
        SlotContent -> fromMaybe "no description available" $ lookup key metaData.slotParameterDescriptions
        ValueContent -> fromMaybe "no description available" $ lookup key metaData.valueParameterDescriptions

      mParameterError = case integerTemplateType of
        SlotContent -> slotError parameterValue
        ValueContent -> valueError parameterValue
    in
      li
        [ classNames [ "mb-1" ] ]
        [ label
            [ classNames [ "block", "mb-0.5" ] ]
            [ text $ key <> ": " <> description ]
        , input
            [ classNames $ Css.input (isJust mParameterError)
            , type_ InputNumber
            , min one
            , onValueInput_ $ SetParameter integerTemplateType key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
                Nothing -> []
        ]

contractReviewScreen :: forall p. State -> HTML p Action
contractReviewScreen state =
  div
    [ classNames [ "mx-auto", "w-22", "bg-white", "p-1" ] ]
    [ text "Summary information about the contract goes here." ]

------------------------------------------------------------
templateLibraryCard :: forall p. Array Template -> HTML p Action
templateLibraryCard templates =
  div_
    [ h2
        [ classNames [ "text-lg", "text-center", "font-bold", "mb-1" ] ]
        [ text "Choose a contract template" ]
    , div
        [ classNames [ "grid", "gap-1", "md:grid-cols-2", "lg:grid-cols-3" ] ]
        (templateBox <$> templates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-1" ] ]
      [ div
          [ classNames [ "flex", "justify-between" ] ]
          [ text template.metaData.contractType
          , button
              [ classNames Css.primaryButton
              , onClick_ $ SetTemplate template
              ]
              [ span_ [ text "Setup" ]
              , span_ [ Icon.navigateNext ]
              ]
          ]
      , h3
          [ classNames [ "font-bold" ] ]
          [ text template.metaData.contractName ]
      , p_
          [ text template.metaData.contractDescription ]
      ]

contractSetupConfirmationCard :: forall p. HTML p Action
contractSetupConfirmationCard =
  div_
    [ p_ [ text "Are you sure?" ]
    , div
        [ classNames [ "flex" ] ]
        [ button
            [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-1" ]
            , onClick_ ToggleSetupConfirmationCard
            ]
            [ text "Cancel" ]
        , button
            [ classNames $ Css.primaryButton <> [ "flex-1" ]
            , onClick_ StartContract
            ]
            [ text "Pay" ]
        ]
    ]
