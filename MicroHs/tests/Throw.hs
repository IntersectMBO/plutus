module Throw where
import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception

delay :: Int -> IO ()
delay i = loop i `seq` return ()

loop :: Int -> Int
loop i = if i == 0 then 0 else loop (i-1)

main :: IO ()
main = do
  th1 <- forkIO $ catch (threadDelay 1000000) (\ (e :: SomeException) -> print e)
  delay 100000
  killThread th1
  delay 100000
  th2 <- forkIO $ catch (newEmptyMVar >>= takeMVar) (\ (e :: SomeException) -> print e)
  delay 100000
  throwTo th2 Overflow
  delay 100000
  th3 <- forkIO $ catch (delay 1000000) (\ (e :: SomeException) -> print e)
  delay 100000
  throwTo th3 UserInterrupt
  delay 100000
