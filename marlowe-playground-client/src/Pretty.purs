module Pretty where

import Prelude
import Data.Array (concat, drop, dropWhile, length, replicate, take)
import Data.BigInteger (BigInteger, format)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.String as String
import Halogen.HTML (HTML, abbr, text)
import Halogen.HTML.Properties (title)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Semantics (Party(..), Payee(..), Token(..))

renderPrettyToken :: forall p i. Token -> HTML p i
renderPrettyToken (Token "" "") = text "ADA"

renderPrettyToken (Token cur tok) = abbr [ title cur ] [ text tok ]

showPrettyToken :: Token -> String
showPrettyToken (Token "" "") = "ADA"

showPrettyToken (Token cur tok) = "\"" <> cur <> " " <> tok <> "\""

renderPrettyParty :: forall p i. MetaData -> Party -> HTML p i
renderPrettyParty _ (PK pkh) = if String.length pkh > 10 then abbr [ title $ "pubkey " <> pkh ] [ text $ String.take 10 pkh ] else text pkh

renderPrettyParty metadata (Role role) = abbr [ title $ "role " <> role <> explanationOrEmptyString ] [ text role ]
  where
  explanationOrEmptyString =
    maybe "" (\explanation -> " – “" <> explanation <> "„")
      $ Map.lookup role metadata.roleDescriptions

showPrettyParty :: Party -> String
showPrettyParty (PK pkh) = "PubKey " <> pkh

showPrettyParty (Role role) = show role

showPrettyMoney :: BigInteger -> String
showPrettyMoney i = format i

renderPrettyPayee :: forall p i. MetaData -> Payee -> Array (HTML p i)
renderPrettyPayee metadata (Account owner2) = [ text "account of ", renderPrettyParty metadata owner2 ]

renderPrettyPayee metadata (Party dest) = [ text "party ", renderPrettyParty metadata dest ]

showBigIntegerAsCurrency :: BigInteger -> Int -> String
showBigIntegerAsCurrency number numDecimals = fromCharArray numberStr
  where
  absValStr = replicate (numDecimals + 1) '0' <> toCharArray (show (if number < zero then -number else number))

  numDigits = length absValStr

  numDigitsBeforeSeparator = numDigits - numDecimals

  prefixStr = if number < zero then [ '-' ] else []

  digitsNoZeros = dropWhile (\x -> x == '0') $ take numDigitsBeforeSeparator absValStr

  digitsBeforeSeparator = if digitsNoZeros == [] then [ '0' ] else digitsNoZeros

  digitsAfterSeparator = take numDecimals $ drop numDigitsBeforeSeparator (concat [ absValStr, replicate numDecimals '0' ])

  numberStr = concat ([ prefixStr, digitsBeforeSeparator ] <> if digitsAfterSeparator /= [] then [ [ '.' ], digitsAfterSeparator ] else [])
