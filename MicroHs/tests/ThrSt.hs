module ThrSt where
import Control.Concurrent
import Control.Concurrent.MVar

thr1 :: IO ()
thr1 = return ()

thr2 :: IO ()
thr2 = error "boo"

thr3 :: IO ()
thr3 = do m <- newEmptyMVar; takeMVar m

thr4 :: IO ()
thr4 = threadDelay 1000000000

main :: IO ()
main = do
  t1 <- forkIO thr1
  t2 <- forkIO thr2
  t3 <- forkIO thr3
  t4 <- forkIO thr4
  t5 <- myThreadId
  threadDelay 100000
  ss <- mapM threadStatus [t1, t2, t3, t4, t5]
  print ss
