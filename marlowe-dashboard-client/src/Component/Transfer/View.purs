module Component.Transfer.View (transfer) where

import Prologue
import Component.Amount (amount)
import Component.Avatar.Types (Size(..)) as Avatar
import Component.Avatar.View (avatar)
import Component.Column (column)
import Component.Column as Column
import Component.Row (row)
import Component.Row as Row
import Component.Transfer.Types (Participant, Termini(..), Transfer)
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..))
import Data.String.Extra (capitalize, endsWith)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, span, text)
import Marlowe.Semantics (Party(..))
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon)

transfer :: forall w i. Transfer -> HTML w i
transfer { sender, recipient, token, quantity, termini } = case termini of
  AccountToAccount from to -> layout from "account" to "account"
  AccountToWallet from to -> layout from "account" to "wallet"
  WalletToAccount from to -> layout from "wallet" to "account"
  where
  layout from fromLabel to toLabel =
    column Column.Cramped [ "border-l-2", "px-2" ]
      [ account from sender fromLabel
      , row Row.Snug [ "px-1", "items-center" ]
          [ icon Icon.South [ "text-purple", "text-xs", "font-semibold" ]
          , amount token quantity [ "text-xs", "text-green" ]
          ]
      , account to recipient toLabel
      ]

-- TODO add read more icon and figure out action. Should it open the contact in
-- the contacts menu?
account :: forall w i. Party -> Participant -> String -> HTML w i
account party { nickname, isCurrentUser } accountTypeLabel =
  row Row.Cramped [ "items-center" ]
    [ avatar
        { nickname: fromMaybe defaultName nickname
        , background: [ "bg-gradient-to-r", "from-purple", "to-lightpurple" ]
        , size: Avatar.Small
        }
    , span [ classNames [ "text-xs" ] ]
        [ text
            $ capitalize
            $ ( case party of
                  PK pk -> accountTypeLabel <> " of " <> pk
                  Role role -> posessive role <> " " <> accountTypeLabel
              )
            <> if isCurrentUser then " (you)" else ""
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
