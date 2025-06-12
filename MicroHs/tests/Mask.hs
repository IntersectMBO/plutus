module Mask where
import Control.Concurrent
import Control.Exception

printMaskingState :: String -> IO ()
printMaskingState s = putStr s >> getMaskingState >>= print

main :: IO ()
main = do
  printMaskingState "start "
  catch (do
            printMaskingState "catch start "
            uninterruptibleMask_ $ do
              printMaskingState "unintr start "
              error "a"
        )
        (\ (_ :: SomeException) -> do
            printMaskingState "handler "
        )
  printMaskingState "end "
