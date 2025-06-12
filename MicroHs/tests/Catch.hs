module Catch(main) where
import Control.Exception
import System.IO

f :: [Int] -> Int
f (_:_) = 99

class C a where
  m :: a -> Int

instance C ()

main :: IO ()
main = do
  let sshow :: String -> String
      sshow = show
      exn :: SomeException -> IO String
      exn e = return (displayException e)
  x <- catch (return ("o" ++ "k")) (\ (_ :: SomeException) -> return "what?")
  putStrLn $ sshow x
  y <- catch (do { error "bang!"; return "yyy" }) exn
  putStrLn $ sshow y
  z <- catch (do { print (f []); return "zzz" })  exn
  putStrLn $ sshow z
  w <- catch (do { print (m ()); return "www" })  exn
  putStrLn $ sshow w
  withFile "Catch.in" ReadMode $ \h -> do
    let ln = hGetLine h
    a <- ln
    b <- ln
    print a
    print b
  withFile "Catch.in" ReadMode $ \h -> do
    let ln = hGetLine h `catch` exn
    a <- ln
    b <- ln
    c <- ln
    print a
    print b
    print c
