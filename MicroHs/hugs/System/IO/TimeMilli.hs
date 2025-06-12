module System.IO.TimeMilli(getTimeMilli) where
import Data.Time
import Data.Time.Clock.POSIX

getTimeMilli :: IO Int
getTimeMilli  = fmap (floor . (1000 *) . toRational . utcTimeToPOSIXSeconds) getCurrentTime
