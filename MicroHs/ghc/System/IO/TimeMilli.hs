module System.IO.TimeMilli(getTimeMilli) where
import Data.Time
import Data.Time.Clock.POSIX

getTimeMilli :: IO Int
getTimeMilli  = floor . (1000 *) . nominalDiffTimeToSeconds . utcTimeToPOSIXSeconds <$> getCurrentTime

