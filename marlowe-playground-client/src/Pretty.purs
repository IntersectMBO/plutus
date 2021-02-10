module Pretty where

import Marlowe.Semantics (Party(..), Payee(..), Token(..))
import Prelude
import Data.BigInteger (BigInteger, format)
import Data.String (length, take)
import Halogen.HTML (HTML, abbr, text)
import Halogen.HTML.Properties (title)

renderPrettyToken :: forall p i. Token -> HTML p i
renderPrettyToken (Token "" "") = text "ADA"

renderPrettyToken (Token cur tok) = abbr [ title cur ] [ text tok ]

showPrettyToken :: Token -> String
showPrettyToken (Token "" "") = "ADA"

showPrettyToken (Token cur tok) = "\"" <> cur <> " " <> tok <> "\""

renderPrettyParty :: forall p i. Party -> HTML p i
renderPrettyParty (PK pkh) = if length pkh > 10 then abbr [ title $ "pubkey " <> pkh ] [ text $ take 10 pkh ] else text pkh

renderPrettyParty (Role role) = abbr [ title $ "role " <> role ] [ text role ]

showPrettyParty :: Party -> String
showPrettyParty (PK pkh) = "PubKey " <> pkh

showPrettyParty (Role role) = show role

showPrettyMoney :: BigInteger -> String
showPrettyMoney i = format i

renderPrettyPayee :: forall p i. Payee -> Array (HTML p i)
renderPrettyPayee (Account owner2) = [ text "account of ", renderPrettyParty owner2 ]

renderPrettyPayee (Party dest) = [ text "party ", renderPrettyParty dest ]
