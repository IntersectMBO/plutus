module Fake.Text
    ( Text
    , pack
    , unpack
    , length
    , splitAt
    , take
    , any
    , filter
    , reverse
    , decimal
    , double
    , decodeUtf8
    , toLower
    , toUpper
    ) where

import Prelude (undefined, Either(..), Char)

data Text = Text

pack _      = Text
unpack :: Text -> [Char]
unpack _ = undefined
length      = undefined
splitAt _ _ = (undefined, undefined)
take        = undefined
filter _    = undefined
reverse     = undefined
any         = undefined
decodeUtf8  = undefined
toLower     = undefined
toUpper     = undefined

decimal :: Text -> Either a (b, c)
decimal = undefined

double :: Text -> Either a (b, c)
double = undefined
