module Sieve(main) where

primes :: [Integer]
primes =
  sieve (from 2)
  where
    from n = n : from (n + 1)
    sieve (p : x) = p : sieve (filter x)
                    where
                      filter (n : x) =
                        if n `rem` p == 0 then filter x
                        else n : filter x

main :: IO ()
main =
  print $ take 100 primes
