module System.RTS(gc, Stats(..), getStats) where
import MiniPrelude
import Prelude qualified ()
import Primitives

gc :: IO ()
gc = primGC

data Stats = Stats
  { cellsAllocated :: Word
  , reductions     :: Word
  } deriving (Show)

getStats :: IO Stats
getStats = do
  (a, r) <- primStats
  return Stats{ cellsAllocated = a, reductions = r }
