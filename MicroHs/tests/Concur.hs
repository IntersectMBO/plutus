module Concur(main) where
import Control.Concurrent
import System.IO

-- Use ::Int to avoid using Integer anywhere since
-- the can change the timing on different platforms
-- (32 vs 64 bit, with or without GMP).

delay :: Int -> IO ()
delay i = loop i `seq` return ()

loop :: Int -> Int
loop i = if i == (0::Int) then (0::Int) else loop (i - (1::Int))

showId :: String -> IO ()
showId s = do
  i <- myThreadId
  putStrLn $ "thread " ++ show i ++ ": " ++ show s

run :: Int -> String -> IO ()
run i s =
  if i == (0::Int) then
    return ()
   else do
    delay (10000::Int)
    putStr s
    hFlush stdout
    run (i - (1::Int)) s

xrun :: Int -> String -> IO ()
xrun i s = do
  delay i
  showId s
  delay (2000::Int)
  run (1000::Int) s

main :: IO ()
main = do
  putStrLn "start"
  forkIO $ xrun (1000::Int) "b"
  forkIO $ xrun (2000::Int) "c"
  xrun (0::Int) "a"
  delay (100000::Int)
  putStrLn "\ndone"
