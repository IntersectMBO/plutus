module Component.Transfer (transfer) where

import Prologue
import Component.Amount (amount)
import Component.Avatar.Types (Size(..)) as Avatar
import Component.Avatar (avatar)
import Component.Column (column)
import Component.Column as Column
import Component.Row (row)
import Component.Row as Row
import Component.Transfer.Types (Account(..), Owner(..), Transfer(..), Wallet(..))
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..))
import Data.String.Extra (capitalize, endsWith)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, span, text)
import Marlowe.Semantics (Party(..), Token(..))
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon)

transfer :: forall w i. Transfer -> HTML w i
transfer = case _ of
  AccountToAccount (Account fromParty fromOwner) (Account toParty toOwner) quantity ->
    layout
      fromParty
      fromOwner
      "account"
      toParty
      toOwner
      "account"
      quantity
  AccountToWallet (Account fromParty fromOwner) (Wallet toParty toOwner) quantity ->
    layout
      fromParty
      fromOwner
      "account"
      toParty
      toOwner
      "wallet"
      quantity
  WalletToAccount (Wallet fromParty fromOwner) (Account toParty toOwner) quantity ->
    layout
      fromParty
      fromOwner
      "wallet"
      toParty
      toOwner
      "account"
      quantity
  where
  layout fromParty fromOwner fromAccountType toParty toOwner toAccountType quantity =
    column Column.Cramped [ "border-l-2", "px-2" ]
      [ account fromParty fromOwner fromAccountType
      , row Row.Snug [ "px-1", "items-center" ]
          [ icon Icon.South [ "text-purple", "text-xs", "font-semibold" ]
          , amount (Token "" "") quantity [ "text-xs", "text-green" ]
          ]
      , account toParty toOwner toAccountType
      ]

-- TODO add read more icon and figure out action. Should it open the contact in
-- the contacts menu?
account :: forall w i. Party -> Owner -> String -> HTML w i
account party owner accountTypeLabel =
  row Row.Cramped [ "items-center" ]
    [ avatar
        { nickname:
            case owner of
              CurrentUser nickname -> nickname
              OtherUser nickname -> fromMaybe defaultName nickname
        , background: [ "bg-gradient-to-r", "from-purple", "to-lightpurple" ]
        , size: Avatar.Small
        }
    , span [ classNames [ "text-xs" ] ]
        [ text
            $ capitalize
            $ case owner of
                CurrentUser _ -> "your" <> " " <> accountTypeLabel
                OtherUser _ -> case party of
                  PK pk -> accountTypeLabel <> " of " <> pk
                  Role role -> posessive role <> " " <> accountTypeLabel
        ]
    ]
  where
  defaultName = case party of
    PK pk -> pk
    Role role -> role

  posessive noun
    | isPlural noun = noun <> "'"
    | otherwise = noun <> "'s"

  isPlural = endsWith $ Pattern "s"
