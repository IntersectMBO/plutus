module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div)
import Css (classNames, hideWhen)
import Css as Css
import Data.Array (mapWithIndex)
import Data.BigInteger (BigInteger)
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.Map (Map, lookup)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (toUnfoldable) as Set
import Data.String (null)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, input, label, li, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), for, id_, list, placeholder, readOnly, type_, value)
import Marlowe.Extended (IntegerTemplateType(..), _slotContent, _valueContent, contractTypeInitials)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Party(..))
import Material.Icons as Icon
import Template.Lenses (_contractName, _contractNickname, _extendedContract, _metaData, _roleWallets, _template, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (roleError, roleWalletsAreValid, slotError, templateContentIsValid, valueError)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList)

contractSetupScreen :: forall p. WalletLibrary -> State -> HTML p Action
contractSetupScreen wallets state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    extendedContract = view (_template <<< _extendedContract) state

    contractNickname = view _contractNickname state

    roleWallets = view _roleWallets state

    templateContent = view _templateContent state

    slotContent = view _slotContent templateContent

    valueContent = view _valueContent templateContent

    termsAreAccessible = roleWalletsAreValid roleWallets wallets

    payIsAccessible = termsAreAccessible && templateContentIsValid templateContent
  in
    div
      [ classNames [ "grid", "grid-rows-contractSetup", "h-full", "overflow-hidden" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "items-center", "px-6", "py-2", "border-b", "border-darkgray" ] ]
          [ a
              -- "-ml-2" shifts things to the left so that the icon lines up properly
              [ classNames [ "flex", "items-center", "font-semibold", "-ml-2" ]
              , onClick_ ToggleTemplateLibraryCard
              ]
              [ Icon.previous
              , span_
                  [ text "Choose template" ]
              ]
          , span
              [ classNames [ "text-sm", "uppercase" ] ]
              [ text contractName ]
          ]
      , contractNicknameDisplay contractName contractNickname
      , div
          [ classNames [] ]
          [ div
              [ classNames [ "h-full", "overflow-y-auto" ] ]
              [ subHeader "top-0" "pb-2" Icon.roles "Roles" true
              , subSection true
                  [ ul
                      [ classNames [] ]
                      $ mapWithIndex (partyInput metaData wallets roleWallets) (Set.toUnfoldable $ getParties extendedContract)
                  ]
              , subHeader "top-12" "pb-2" Icon.terms "Terms" termsAreAccessible
              , subSection termsAreAccessible
                  [ ul
                      [ classNames [ "mb-4" ] ]
                      $ mapWithIndex (parameterInput metaData SlotContent) (Map.toUnfoldable slotContent)
                  , ul_
                      $ mapWithIndex (parameterInput metaData ValueContent) (Map.toUnfoldable valueContent)
                  ]
              , subHeader "top-24" "pb-0" Icon.pay "Review and pay" payIsAccessible
              , subSection payIsAccessible
                  [ div
                      [ classNames [ "mb-4", "bg-white", "p-4", "shadow", "rounded-lg" ] ]
                      [ text "Summary information about the contract goes here." ]
                  , div
                      [ classNames [ "flex", "justify-end", "pb-8" ] ]
                      [ button
                          [ classNames Css.primaryButton
                          , onClick_ $ ToggleSetupConfirmationCard
                          ]
                          [ text "Pay" ]
                      ]
                  ]
              ]
          ]
      ]

contractNicknameDisplay :: forall p. String -> String -> HTML p Action
contractNicknameDisplay contractName contractNickname =
  div
    [ classNames [ "ml-12", "border-l", "border-darkgray" ] ]
    [ div
        [ classNames [ "mx-auto", "max-w-xs", "px-6", "pt-4", "pb-2" ] ]
        [ input
            [ classNames $ (Css.inputDark $ null contractNickname) <> [ "bg-transparent", "font-semibold" ]
            , type_ InputText
            , placeholder "Contract name *"
            , value contractNickname
            , onValueInput_ SetContractNickname
            ]
        ]
    ]

subHeader :: forall p. String -> String -> HTML p Action -> String -> Boolean -> HTML p Action
subHeader topMargin bottomPadding icon title accessible =
  div
    [ classNames [ "ml-12", "border-l", "border-darkgray", "sticky", "z-10", topMargin, bottomPadding, "bg-grayblue" ] ]
    [ div
        [ classNames [ "flex", "items-center" ] ]
        [ span
            [ classNames $ Css.iconCircle accessible <> [ "-ml-5" ] ]
            [ icon ]
        , h2
            [ classNames [ "py-1", "px-2", "text-lg", "font-semibold" ] ]
            [ text title ]
        , hr [ classNames [ "flex-1" ] ]
        ]
    ]

subSection :: forall p. Boolean -> Array (HTML p Action) -> HTML p Action
subSection accessible content =
  div
    [ classNames $ [ "ml-12", "border-l", "border-darkgray", "py-2" ] <> (hideWhen $ not accessible) ]
    [ div
        [ classNames [ "mx-auto", "max-w-xs", "px-6" ] ]
        content
    ]

partyInput :: forall p. MetaData -> WalletLibrary -> Map String String -> Int -> Party -> HTML p Action
partyInput metaData wallets roleWallets index (PK pubKey) =
  li
    [ classNames [ "mb-4", "last:mb-0" ] ]
    [ label
        [ classNames [ "block", "text-sm" ]
        , for pubKey
        ]
        [ text $ "Party " <> (show $ index + 1) ]
    , input
        [ classNames $ Css.input false <> [ "shadow" ]
        , id_ pubKey
        , type_ InputText
        , value pubKey
        , readOnly true
        ]
    ]

partyInput metaData wallets roleWallets index (Role tokenName) =
  let
    description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions

    assigned = fromMaybe "" $ lookup tokenName roleWallets

    mRoleError = roleError assigned wallets
  in
    li
      [ classNames [ "mb-4", "last:mb-0" ] ]
      [ label
          [ classNames [ "block", "text-sm" ]
          , for tokenName
          ]
          [ span
              [ classNames [ "font-bold" ] ]
              [ text $ "Role " <> (show $ index + 1) <> " (" <> tokenName <> ")*" ]
          , br_
          , text description
          ]
      , div
          [ classNames [ "relative" ] ]
          [ input
              [ classNames $ Css.input (isJust mRoleError) <> [ "shadow", "pr-10" ]
              , id_ tokenName
              , type_ InputText
              , list "walletNicknames"
              , onValueInput_ $ SetRoleWallet tokenName
              , value assigned
              ]
          , button
              [ classNames [ "absolute", "top-3", "right-3" ]
              , onClick_ $ ToggleCreateWalletCard tokenName
              ]
              [ Icon.addCircle ]
          ]
      , div
          [ classNames Css.inputError ]
          $ case mRoleError of
              Just roleError -> [ text $ show roleError ]
              Nothing -> []
      , nicknamesDataList wallets
      ]

parameterInput :: forall p. MetaData -> IntegerTemplateType -> Int -> Tuple String BigInteger -> HTML p Action
parameterInput metaData SlotContent index (key /\ parameterValue) =
  let
    description = fromMaybe "no description available" $ lookup key metaData.slotParameterDescriptions

    mParameterError = slotError parameterValue
  in
    li
      [ classNames [ "mb-4", "last:mb-0" ] ]
      [ label
          [ classNames [ "block", "text-sm" ]
          , for $ "slot-" <> key
          ]
          [ span
              [ classNames [ "font-bold" ] ]
              [ text $ "Timeout " <> (show $ index + 1) <> " (" <> key <> ")*" ]
          , br_
          , text description
          ]
      , input
          [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
          , id_ $ "slot-" <> key
          , type_ InputDatetimeLocal
          -- FIXME: convert datetime to slot
          , onValueInput_ $ SetParameter SlotContent key <<< BigInteger.fromString
          -- FIXEME: convert slot to datetime
          , value $ show parameterValue
          ]
      , div
          [ classNames Css.inputError ]
          $ case mParameterError of
              Just parameterError -> [ text $ show parameterError ]
              Nothing -> []
      ]

parameterInput metaData ValueContent index (key /\ parameterValue) =
  let
    description = fromMaybe "no description available" $ lookup key metaData.valueParameterDescriptions

    mParameterError = valueError parameterValue
  in
    li
      [ classNames [ "mb-4", "last:mb-0" ] ]
      [ label
          [ classNames [ "block", "text-sm" ]
          , for $ "value-" <> key
          ]
          [ span
              [ classNames [ "font-bold" ] ]
              [ text $ "Value " <> (show $ index + 1) <> " (" <> key <> ")*" ]
          , br_
          , text description
          ]
      , input
          [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
          , id_ $ "value-" <> key
          , type_ InputNumber
          , onValueInput_ $ SetParameter ValueContent key <<< BigInteger.fromString
          , value $ show parameterValue
          ]
      , div
          [ classNames Css.inputError ]
          $ case mParameterError of
              Just parameterError -> [ text $ show parameterError ]
              Nothing -> []
      ]

------------------------------------------------------------
templateLibraryCard :: forall p. Array ContractTemplate -> HTML p Action
templateLibraryCard templates =
  div_
    [ h2
        [ classNames [ "text-lg", "text-center", "font-semibold", "mb-4" ] ]
        [ text "Choose a contract template" ]
    , div
        [ classNames [ "grid", "gap-4", "md:grid-cols-2", "lg:grid-cols-3" ] ]
        (templateBox <$> templates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-4" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "mb-4" ] ]
          [ div
              [ classNames [ "flex", "align-top" ] ]
              [ span
                  [ classNames [ "text-2xl", "font-semibold", "mr-2" ] ]
                  [ text $ contractTypeInitials template.metaData.contractType ]
              , span
                  [ classNames [ "uppercase" ] ]
                  [ text $ template.metaData.contractName ]
              ]
          , button
              [ classNames Css.primaryButton
              , onClick_ $ SetTemplate template
              ]
              [ span [ classNames [ "mr-2" ] ] [ text "Setup" ]
              , span_ [ Icon.east ]
              ]
          ]
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
            [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
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
