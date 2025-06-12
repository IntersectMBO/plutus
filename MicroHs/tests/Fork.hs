module Fork where
import Control.Concurrent

delay :: Int -> IO ()
delay i = loop i `seq` return ()

loop :: Int -> Int
loop i = if i == 0 then 0 else loop (i-1)

fork :: IO ()
fork = putStrLn "fork done"

main :: IO ()
main = do
  forkIO fork
  delay 100000
  putStrLn "main done"
