module Blinky(main) where
import Prelude

main :: IO ()
main = blinky (500::Int)

blinky :: Int -> IO ()
blinky n | n > 1000 = return ()
blinky n = do
  oneByOne n True
  oneByOne n False
  blinky (n + 1)

oneByOne :: Int -> Bool -> IO ()
oneByOne n on = forM_ [0..3] $ \ led -> do
  setLed led on
  wait (n + led)

foreign import ccall "set_led" set_led :: Int -> Int -> IO ()
foreign import ccall "busy_wait" busy_wait :: Int -> IO ()

setLed :: Int -> Bool -> IO ()
setLed led on = set_led led $ if on then 1 else 0

wait :: Int -> IO ()
wait n = busy_wait (n*300)

loop :: Int -> ()
loop n = if n == 0 then () else loop (n - 1)
