module MVar where
import Control.Concurrent
import Control.Concurrent.MVar

delay :: Int -> IO ()
delay i = loop i `seq` return ()

loop :: Int -> Int
loop i = if i == 0 then 0 else loop $! (i-1)

fun :: MVar Int -> IO ()
fun mv = do
  putStrLn "fun A"
  i <- takeMVar mv
  print i
  putStrLn "fun B"

main :: IO ()
main = do
  test1
  putStrLn "---"
  test2

test1 :: IO ()
test1 = do
  putStrLn "test1 A"
  mvar <- newEmptyMVar
  forkIO (fun mvar)
  putStrLn "test1 B"
  delay 100000
  putStrLn "test1 C"
  putMVar mvar 999
  putStrLn "test1 D"
  putMVar mvar 888
  putStrLn "test1 E"
  forkIO (delay 100000 >> fun mvar)
  putMVar mvar 777
  putStrLn "test1 F"
  delay 100000
  fun mvar
  delay 100000
  putStrLn "test1 G"

test2 :: IO ()
test2 = do
  mvar1 <- newEmptyMVar
  tryTakeMVar mvar1 >>= print
  putStrLn "test2 A"
  putMVar mvar1 (111::Int)
  putStrLn "test2 B"
  tryPutMVar mvar1 222 >>= print
  tryTakeMVar mvar1 >>= print
  tryPutMVar mvar1 333 >>= print

  mvar2 <- newMVar (333::Int)
  tryReadMVar mvar2 >>= print
  tryReadMVar mvar2 >>= print
