module System.IO.TimeMilli(getTimeMilli) where
import MiniPrelude
import Prelude qualified ()

foreign import ccall "GETTIMEMILLI" c_getTimeMilli :: IO Int

getTimeMilli :: IO Int
getTimeMilli = c_getTimeMilli
