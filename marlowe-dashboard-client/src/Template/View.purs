module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Array (filter, mapWithIndex)
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.List (toUnfoldable) as List
import Data.Map (Map, lookup, values)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String (null)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, input, label, li, p, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), enabled, for, id_, placeholder, readOnly, type_, value)
import Humanize (humanizeValue)
import InputField.Types (State) as InputField
import InputField.Types (inputErrorToString)
import InputField.View (renderInput)
import Marlowe.Extended (contractTypeInitials)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Market (contractTemplates)
import Marlowe.PAB (contractCreationFee)
import Marlowe.Semantics (Assets, Slot, TokenName)
import Marlowe.Template (TemplateContent, _valueContent)
import Material.Icons (Icon(..), icon_)
import Template.Format (formatText)
import Template.Lenses (_contractName, _contractNickname, _metaData, _roleWalletInputs, _slotContentStrings, _template, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (RoleError, roleWalletsAreValid, slotError, templateContentIsValid, valueError)
import WalletData.Lenses (_walletNickname)
import WalletData.State (adaToken, getAda)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList, nicknamesDataListId)

contractSetupScreen :: forall p. WalletLibrary -> Slot -> State -> HTML p Action
contractSetupScreen walletLibrary currentSlot state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    contractNickname = view _contractNickname state

    roleWalletInputs = view _roleWalletInputs state

    templateContent = view _templateContent state

    slotContentStrings = view _slotContentStrings state

    termsAreAccessible = roleWalletsAreValid roleWalletInputs

    payIsAccessible = termsAreAccessible && templateContentIsValid templateContent slotContentStrings currentSlot
  in
    div
      [ classNames [ "grid", "grid-rows-contract-setup", "max-h-full", "overflow-hidden" ] ]
      [ navigationBar contractName
      , contractNicknameDisplay contractName contractNickname
      , div -- the containing grid sets the height of this div
          [ classNames [ "px-4", "md:px-5pc" ] ]
          [ div -- and then this fills that height fully
              [ classNames [ "h-full", "overflow-y-auto" ] ]
              [ subHeader "top-0" true Roles "Roles" true
              , roleInputs walletLibrary metaData roleWalletInputs
              , subHeader "top-10" true Terms "Terms" termsAreAccessible
              , parameterInputs currentSlot metaData templateContent slotContentStrings termsAreAccessible
              , subHeader "top-20" false Pay "Review and pay" payIsAccessible
              , reviewAndPay payIsAccessible metaData
              ]
          ]
      ]

navigationBar :: forall p. String -> HTML p Action
navigationBar contractName =
  div
    [ classNames [ "flex", "justify-between", "items-center", "px-4", "py-2", "border-b", "border-gray", "md:px-5pc" ] ]
    [ a
        -- "-ml-1" makes the icon line up properly
        [ classNames [ "flex", "items-center", "font-semibold", "-ml-1" ]
        , onClick_ OpenTemplateLibraryCard
        ]
        [ icon_ Previous
        , span_
            [ text "Choose template" ]
        ]
    , span
        [ classNames [ "text-sm", "uppercase" ] ]
        [ text contractName ]
    ]

contractNicknameDisplay :: forall p. String -> String -> HTML p Action
contractNicknameDisplay contractName contractNickname =
  div
    [ classNames [ "px-4", "md:px-5pc" ] ]
    [ div
        [ classNames [ "ml-5", "border-l", "border-gray", "pt-2" ] ]
        [ div
            [ classNames [ "max-w-sm", "mx-auto", "px-4", "pt-2" ] ]
            [ input
                [ classNames
                    -- TODO: Once we remove the readOnly, remove this filter. I tried adding "text-black" to the end of the array
                    
                    --       but the browser does not respect ordering and for some reason "text-darkgray was winning"
                    
                    $ filter (not <<< eq "text-darkgray")
                    $ (Css.input $ null contractNickname)
                    <> [ "font-semibold" ]
                , type_ InputText
                , placeholder "Contract name *"
                , value contractNickname
                -- TODO: We can allow users to provide custom contract nicknames when we are connecting to the
                -- metadata server. For now, however, we have no way of sharing this information, so we just
                -- make it readonly (it is set to equal the contract name initially).
                , readOnly true
                , onValueInput_ SetContractNickname
                ]
            ]
        ]
    ]

subHeader :: forall p. String -> Boolean -> Icon -> String -> Boolean -> HTML p Action
subHeader topMargin border i title accessible =
  div
    [ classNames $ [ "ml-5", "sticky", "z-10", topMargin, "pb-2", "bg-grayblue" ] <> applyWhen border [ "border-l", "border-gray" ] ]
    [ div
        [ classNames [ "flex", "items-center" ] ]
        [ span
            [ classNames $ Css.iconCircle accessible <> [ "-ml-4" ] ]
            [ icon_ i ]
        , h2
            [ classNames [ "py-1", "px-2", "text-lg", "font-semibold" ] ]
            [ text title ]
        , hr [ classNames $ [ "flex-1" ] <> hideWhen (not accessible) ]
        ]
    ]

-- We range over roleWalletInputs rather than all the parties in the contract. This excludes any `PK` parties.
-- At the moment, this is a good thing: we don't have a design for them, and we only use a `PK` party in one
-- special case, where it is read-only and would be confusing to show the user anyway. But if we ever need to
-- use `PK` inputs properly (and make them editable) we will have to rethink this.
roleInputs :: forall p. WalletLibrary -> MetaData -> Map TokenName (InputField.State RoleError) -> HTML p Action
roleInputs walletLibrary metaData roleWalletInputs =
  subSection true true
    [ ul_
        $ mapWithIndex roleInput
        $ Map.toUnfoldable roleWalletInputs
    ]
  where
  roleInput index (tokenName /\ roleWalletInput) =
    let
      description = fromMaybe "no description available" $ lookup tokenName metaData.roleDescriptions
    in
      li
        [ classNames [ "mb-2", "last:mb-0" ] ]
        [ label
            [ classNames [ "block", "text-sm", "mb-2" ]
            , for tokenName
            ]
            [ span
                [ classNames [ "font-bold" ] ]
                [ text $ "Role " <> (show $ index + 1) <> " (" <> tokenName <> ")*" ]
            , br_
            , span_ $ formatText description
            ]
        , div
            [ classNames [ "relative" ] ]
            [ RoleWalletInputAction tokenName <$> renderInput roleWalletInput (roleWalletInputDisplayOptions tokenName)
            , button
                [ classNames [ "absolute", "top-4", "right-4" ]
                , onClick_ $ OpenCreateWalletCard tokenName
                ]
                [ icon_ AddCircle ]
            ]
        , nicknamesDataList walletLibrary
        ]

  roleWalletInputDisplayOptions tokenName =
    { baseCss: Css.inputCardNoFocus
    , additionalCss: [ "pr-9" ]
    , id_: tokenName
    , placeholder: "Choose any nickname"
    , readOnly: false
    , datalistId: Just nicknamesDataListId
    , valueOptions: List.toUnfoldable $ values $ view _walletNickname <$> walletLibrary
    }

parameterInputs :: forall p. Slot -> MetaData -> TemplateContent -> Map String String -> Boolean -> HTML p Action
parameterInputs currentSlot metaData templateContent slotContentStrings accessible =
  let
    valueContent = view _valueContent templateContent
  in
    subSection accessible true
      [ ul
          [ classNames [ "mb-4" ] ]
          $ mapWithIndex slotInput (Map.toUnfoldable slotContentStrings)
      , ul_
          $ mapWithIndex valueInput (Map.toUnfoldable valueContent)
      ]
  where
  slotInput index (key /\ dateTimeString) =
    let
      description = fromMaybe "no description available" $ lookup key metaData.slotParameterDescriptions

      mParameterError = slotError currentSlot dateTimeString
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
            , span_ $ formatText description
            ]
        , input
            [ classNames $ Css.inputCard (isJust mParameterError)
            , id_ $ "slot-" <> key
            , type_ InputDatetimeLocal
            , onValueInput_ $ SetSlotContent key
            , value dateTimeString
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ inputErrorToString parameterError ]
                Nothing -> []
        ]

  valueInput index (key /\ parameterValue) =
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
            , span_ $ formatText description
            ]
        , input
            [ classNames $ Css.inputCard (isJust mParameterError)
            , id_ $ "value-" <> key
            , type_ InputNumber
            , onValueInput_ $ SetValueContent key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ inputErrorToString parameterError ]
                Nothing -> []
        ]

reviewAndPay :: forall p. Boolean -> MetaData -> HTML p Action
reviewAndPay accessible metaData =
  subSection accessible false
    [ div
        [ classNames $ [ "mb-4", "bg-white", "p-4", "shadow", "rounded" ] ]
        [ contractTitle metaData
        , hr [ classNames [ "my-4" ] ]
        , div_
            [ p
                [ classNames [ "text-sm" ] ]
                [ text "Fee to pay:" ]
            , p
                [ classNames Css.funds ]
                [ text $ humanizeValue adaToken contractCreationFee ]
            ]
        ]
    , div
        [ classNames [ "flex", "justify-end", "mb-4" ] ]
        [ button
            [ classNames Css.primaryButton
            , onClick_ $ OpenSetupConfirmationCard
            ]
            [ text "Pay" ]
        ]
    ]

subSection :: forall p. Boolean -> Boolean -> Array (HTML p Action) -> HTML p Action
subSection accessible border content =
  div
    [ classNames $ [ "py-2", "ml-5" ] <> applyWhen border [ "border-l", "border-gray" ] <> (hideWhen $ not accessible) ]
    [ div
        [ classNames $ [ "max-w-sm", "mx-auto", "px-4" ] ]
        content
    ]

------------------------------------------------------------
templateLibraryCard :: forall p. HTML p Action
templateLibraryCard =
  div
    [ classNames [ "md:px-5pc", "p-4" ] ]
    [ h2
        [ classNames [ "text-lg", "font-semibold", "mb-4" ] ]
        [ text "Choose a contract template" ]
    , div
        [ classNames [ "grid", "gap-4", "md:grid-cols-2", "xl:grid-cols-3" ] ]
        (templateBox <$> contractTemplates)
    ]
  where
  templateBox template =
    div
      [ classNames [ "bg-white", "p-4" ] ]
      [ div
          [ classNames [ "flex", "justify-between", "items-start", "mb-4" ] ]
          [ contractTitle template.metaData
          , button
              [ classNames $ Css.primaryButton <> Css.withIcon ArrowRight <> [ "min-w-button" ]
              , onClick_ $ SetTemplate template
              ]
              [ text "Setup" ]
          ]
      , p_ $ formatText template.metaData.contractDescription
      ]

-- TODO: This helper is really similar to contractCard in ContractHome.View, see if it makes sense to factor a component out
contractTitle :: forall p. MetaData -> HTML p Action
contractTitle metaData =
  div
    [ classNames [ "flex", "items-start", "mr-1" ] ]
    [ span
        [ classNames [ "text-2xl", "leading-none", "font-semibold" ] ]
        [ text $ contractTypeInitials metaData.contractType ]
    , span
        [ classNames [ "text-xs", "uppercase", "ml-2" ] ]
        [ text $ metaData.contractName ]
    ]

-- TODO: This is a lot like the `actionConfirmationCard` in `Contract.View`. Consider factoring out a shared component.
contractSetupConfirmationCard :: forall p. Assets -> HTML p Action
contractSetupConfirmationCard assets =
  let
    hasSufficientFunds = getAda assets >= contractCreationFee
  in
    div_
      [ div [ classNames [ "flex", "font-semibold", "justify-between", "bg-lightgray", "p-5" ] ]
          [ span_ [ text "Demo wallet balance:" ]
          , span_ [ text $ humanizeValue adaToken $ getAda assets ]
          ]
      , div [ classNames [ "px-5", "pb-6", "md:pb-8" ] ]
          [ p
              [ classNames [ "mt-4", "text-sm", "font-semibold" ] ]
              [ text "Confirm payment of:" ]
          , p
              [ classNames [ "mb-4", "text-purple", "font-semibold", "text-2xl" ] ]
              [ text $ humanizeValue adaToken contractCreationFee ]
          , div
              [ classNames [ "flex" ] ]
              [ button
                  [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-2" ]
                  , onClick_ CloseSetupConfirmationCard
                  ]
                  [ text "Cancel" ]
              , button
                  [ classNames $ Css.primaryButton <> [ "flex-1" ]
                  , onClick_ StartContract
                  , enabled hasSufficientFunds
                  ]
                  [ text "Pay and run" ]
              ]
          , div
              [ classNames [ "mt-4", "text-sm", "text-red" ] ]
              if hasSufficientFunds then
                []
              else
                [ text "You have insufficient funds to initialise this contract." ]
          ]
      ]
