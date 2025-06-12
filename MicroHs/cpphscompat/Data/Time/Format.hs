module Data.Time.Format(module Data.Time.Format) where
import Data.Time.Clock

data TimeLocale

formatTime :: TimeLocale -> String -> UTCTime -> String
formatTime _ _ (UTCTime t) = show t ++ "s"
