module Readline(main) where
import System.Console.SimpleReadline

main :: IO ()
main = do
  putStrLn "Type 'quit' to quit."
  loop

loop :: IO ()
loop = do
  s <- getInputLineHist "hist.txt" "% "
  case s of
    Just "quit" -> putStrLn "Bye"
    _           -> do putStrLn $ showMaybe showString s; loop

