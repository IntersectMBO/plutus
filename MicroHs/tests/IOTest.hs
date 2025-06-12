module IOTest(module IOTest) where
import System.IO as IO
import System.IO.TimeMilli
import System.Environment
import Debug.Trace

foo :: IO ()
foo = do
  putStrLn "foo 1"
  putStrLn "foo 2"

main :: IO ()
main = do
  tstart <- getTimeMilli
  putChar 'a'
  putChar 'b'
  c <- getChar
  putStrLn [c,c,c]
  let { p = putStrLn "hello" }
  p
  p
  p
  hout <- openFile "test.tmp" WriteMode
  hPutChar hout 'a'
  hPutChar hout 'z'
  hClose hout
  hin <- openFile "test.tmp" ReadMode
  c1 <- hGetChar hin
  c2 <- hGetChar hin
  print (c1, c2)
  writeFile "test2.tmp" "more\n"
  s <- readFile "test2.tmp"
  print s
  foo
  print $ trace "tracing" (5::Int)
  as <- getArgs
  print as
  print $ seq ((1::Int) + (2::Int)) (5::Int)
  print $ seq ((1::Int) + trace "seq" (2::Int)) (5::Int)
  tend <- getTimeMilli
  print (tend - tstart) ++ "ms execution time"
