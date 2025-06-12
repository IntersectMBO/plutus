module Nfib(main, nfib) where
import System.IO.TimeMilli (getTimeMilli)

nfib :: Int -> Int
nfib n =
  case n < 2 of
    False -> nfib (n - 1) + nfib (n - 2) + 1
    True  -> 1

main :: IO ()
main = do
  t1 <- getTimeMilli
  let r = nfib 37
  print r
  t2 <- getTimeMilli
  putStrLn $ "nfib/s = " ++ show (r `quot` (t2 - t1)) ++ "k"

-- Typical nfib/s is 10M
-- mhs
-- 126491971 / 15.68 = 8.07M
-- ghc
-- 126491971 / 0.236 = 535M
