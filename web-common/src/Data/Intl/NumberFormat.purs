-- TODO: There is a purescript-intl repo on GitHub, but it hasn't been updated in 4 years
-- and only includes things for Intl.DateTimeFormat. We need Intl.NumberFormat here. This
-- is an absolutely minimal implementation, just enough to do what we need here. It would
-- potentially be nice to expand it and do it properly.
module Data.Intl.NumberFormat (format) where

foreign import format_ :: Number -> String

format :: Number -> String
format = format_
