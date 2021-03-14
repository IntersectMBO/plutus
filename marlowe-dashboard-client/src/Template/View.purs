module Template.View
  ( contractSetupScreen
  , templateLibraryCard
  , contractSetupConfirmationCard
  ) where

import Prelude hiding (div)
import Css (applyWhen, classNames, hideWhen, toggleWhen)
import Css as Css
import Data.Array (mapWithIndex)
import Data.BigInteger (fromString) as BigInteger
import Data.Lens (view)
import Data.Map (Map, lookup)
import Data.Map (toUnfoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Set (toUnfoldable) as Set
import Data.String (null)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, input, label, li, p_, span, span_, text, ul, ul_)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), for, id_, list, placeholder, readOnly, type_, value)
import Marlowe.Extended (Contract, TemplateContent, _valueContent, contractTypeInitials)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Party(..), Slot)
import Material.Icons as Icon
import Template.Lenses (_contractName, _contractNickname, _extendedContract, _metaData, _roleWallets, _slotContentStrings, _template, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (roleError, roleWalletsAreValid, slotError, templateContentIsValid, valueError)
import WalletData.Types (WalletLibrary)
import WalletData.View (nicknamesDataList)

contractSetupScreen :: forall p. WalletLibrary -> Slot -> State -> HTML p Action
contractSetupScreen wallets currentSlot state =
  let
    metaData = view (_template <<< _metaData) state

    contractName = view (_contractName) metaData

    extendedContract = view (_template <<< _extendedContract) state

    contractNickname = view _contractNickname state

    roleWallets = view _roleWallets state

    templateContent = view _templateContent state

    slotContentStrings = view _slotContentStrings state

    termsAreAccessible = roleWalletsAreValid roleWallets wallets

    payIsAccessible = termsAreAccessible && templateContentIsValid templateContent slotContentStrings currentSlot
  in
    -- This screen needs to have sticky subHeaders _and_ have the sections initially beneath
    -- those subHeaders go to the right of them on larger screens. Since the sticky subHeaders
    -- need to have the same parent div (or the stickyness doesn't work), the only way I could
    -- think to do the layout for larger screens was with a grid. However (bear with me)...
    -- Cells in the same row on a grid are all the same height, which makes the cells containing
    -- the subHeaders bigger than they need to be, which in turn pushes the subHeaders above
    -- their sticky top limit when you scroll down. The only solution I could come up with was
    -- to have _two_ divs next to each other, the first with the subHeaders and the inputs, and
    -- the second with a _copy_ of the inputs. The second one is hidden on small screens. On
    -- larger screens, we show the subHeaders from the first and make those inputs _invisible_
    -- (not hidden) so that they fill the appropriate space and make the subHeaders line up as
    -- they should.
    div
      [ classNames [ "grid", "grid-rows-contract-setup", "h-full", "overflow-hidden" ] ]
      [ navigationBar contractName
      , contractNicknameDisplay contractName contractNickname
      , div_ -- the containing grid sets the height of this div
          [ div -- and then this fills that height fully
              [ classNames [ "h-full", "overflow-y-auto" ] ]
              [ div -- and then this div creates the grid (not necessarily full height) on large screens
                  [ classNames [ "lg:grid", "lg:grid-cols-contract-setup" ] ]
                  [ div -- this is all we need for small screens
                      [ classNames [] ]
                      [ subHeader "top-0" true Icon.roles "Roles" true
                      , roleInputs true wallets extendedContract metaData roleWallets
                      , subHeader "top-12" true Icon.terms "Terms" termsAreAccessible
                      , parameterInputs true wallets currentSlot metaData templateContent slotContentStrings roleWallets termsAreAccessible
                      , subHeader "top-24" false Icon.pay "Review and pay" payIsAccessible
                      , reviewAndPay true payIsAccessible metaData
                      ]
                  , div -- for medium screens we show the second column
                      [ classNames [ "hidden", "lg:block" ] ]
                      [ roleInputs false wallets extendedContract metaData roleWallets
                      , parameterInputs false wallets currentSlot metaData templateContent slotContentStrings roleWallets termsAreAccessible
                      , reviewAndPay false payIsAccessible metaData
                      ]
                  , div -- for large screens we have an empty third column
                      [ classNames [ "hidden", "lg:block" ] ]
                      []
                  ]
              ]
          ]
      ]

navigationBar :: forall p. String -> HTML p Action
navigationBar contractName =
  div
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

contractNicknameDisplay :: forall p. String -> String -> HTML p Action
contractNicknameDisplay contractName contractNickname =
  div
    [ classNames [ "lg:grid", "lg:grid-cols-contract-setup" ] ]
    [ div [ classNames [ "hidden", "lg:block", "ml-11", "border-l", "border-darkgray" ] ] []
    , div
        [ classNames [ "ml-11", "border-l", "border-darkgray", "lg:ml-0", "lg:border-0" ] ]
        [ div
            [ classNames [ "max-w-sm", "lg:w-sm", "mx-auto", "px-6", "pt-4", "pb-2" ] ]
            [ input
                [ classNames $ (Css.inputDark $ null contractNickname) <> [ "bg-transparent", "font-semibold" ]
                , type_ InputText
                , placeholder "Contract name *"
                , value contractNickname
                , onValueInput_ SetContractNickname
                ]
            ]
        ]
    , div [ classNames [ "hidden", "lg:block" ] ] []
    ]

subHeader :: forall p. String -> Boolean -> HTML p Action -> String -> Boolean -> HTML p Action
subHeader topMargin border icon title accessible =
  div
    [ classNames $ [ "ml-11", "sticky", "z-10", topMargin, "pb-2", "bg-grayblue" ] <> applyWhen border [ "border-l", "border-darkgray" ] ]
    [ div
        [ classNames [ "flex", "items-center" ] ]
        [ span
            [ classNames $ Css.iconCircle accessible <> [ "-ml-5" ] ]
            [ icon ]
        , h2
            [ classNames [ "py-1", "px-2", "text-lg", "font-semibold" ] ]
            [ text title ]
        , hr [ classNames $ [ "flex-1", "mr-6", "lg:mr-0" ] <> hideWhen (not accessible) ]
        ]
    ]

roleInputs :: forall p. Boolean -> WalletLibrary -> Contract -> MetaData -> Map String String -> HTML p Action
roleInputs forMobile wallets extendedContract metaData roleWallets =
  subSection forMobile true true
    [ ul
        [ classNames [] ]
        $ mapWithIndex partyInput
        $ Set.toUnfoldable
        $ getParties extendedContract
    ]
  where
  partyInput index (PK pubKey) =
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

  partyInput index (Role tokenName) =
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

parameterInputs :: forall p. Boolean -> WalletLibrary -> Slot -> MetaData -> TemplateContent -> Map String String -> Map String String -> Boolean -> HTML p Action
parameterInputs forMobile wallets currentSlot metaData templateContent slotContentStrings roleWallets accessible =
  let
    valueContent = view _valueContent templateContent
  in
    subSection forMobile accessible true
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

      mParameterError = slotError dateTimeString currentSlot
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
            , onValueInput_ $ SetSlotContent key
            -- FIXEME: convert slot to datetime
            , value dateTimeString
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
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
            , text description
            ]
        , input
            [ classNames $ Css.input (isJust mParameterError) <> [ "shadow" ]
            , id_ $ "value-" <> key
            , type_ InputNumber
            , onValueInput_ $ SetValueContent key <<< BigInteger.fromString
            , value $ show parameterValue
            ]
        , div
            [ classNames Css.inputError ]
            $ case mParameterError of
                Just parameterError -> [ text $ show parameterError ]
                Nothing -> []
        ]

reviewAndPay :: forall p. Boolean -> Boolean -> MetaData -> HTML p Action
reviewAndPay forMobile accessible metaData =
  subSection forMobile accessible false
    [ div
        [ classNames $ [ "mb-4", "bg-white", "p-4", "shadow", "rounded-lg" ] <> applyWhen (not forMobile) [ "mt-2" ] ]
        [ contractTitle metaData ]
    , div
        [ classNames [ "flex", "justify-end", "mb-4" ] ]
        [ button
            [ classNames Css.primaryButton
            , onClick_ $ ToggleSetupConfirmationCard
            ]
            [ text "Pay" ]
        ]
    ]

subSection :: forall p. Boolean -> Boolean -> Boolean -> Array (HTML p Action) -> HTML p Action
subSection forMobile accessible border content =
  div
    [ classNames
        $ [ "py-2" ]
        <> toggleWhen forMobile [ "ml-11", "lg:-mr-12" ] [ "mb-2" ]
        <> applyWhen (forMobile && border) [ "border-l", "border-darkgray" ]
        <> applyWhen (forMobile && accessible) [ "lg:-mt-10" ]
    ]
    [ div
        -- hide this div instead of the parent, because we want the parent to always take up
        -- its alloted space in the grid
        [ classNames $ [ "max-w-sm", "mx-auto", "px-6" ] <> (hideWhen $ not accessible) <> (applyWhen forMobile [ "lg:invisible" ]) ]
        content
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
          [ contractTitle template.metaData
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

contractTitle :: forall p. MetaData -> HTML p Action
contractTitle metaData =
  div
    [ classNames [ "flex", "align-top" ] ]
    [ span
        [ classNames [ "text-2xl", "font-semibold", "mr-2" ] ]
        [ text $ contractTypeInitials metaData.contractType ]
    , span
        [ classNames [ "uppercase" ] ]
        [ text $ metaData.contractName ]
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
