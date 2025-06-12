-- A hack to be able to compile cpphs.
-- We need a proper package for this.
module Data.Time.Clock(
  UTCTime(..),
  getCurrentTime,
  ) where
import Prelude
import System.IO.TimeMilli

-- Second since 1970, probably
newtype UTCTime = UTCTime Int
  deriving (Show)

getCurrentTime :: IO UTCTime
getCurrentTime = do
  t <- getTimeMilli
  return $ UTCTime $ t `quot` 1000
