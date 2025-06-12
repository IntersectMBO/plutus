module ST(main) where
import Control.Monad.ST
import Data.STRef
import Debug.Trace

facST :: forall s . Int -> ST s Int
facST n = do
  ri <- newSTRef 1
  rr <- newSTRef 1
  let loop = do
        i <- readSTRef ri
        if i > n then
          return ()
         else do
          writeSTRef ri (i + 1)
          modifySTRef rr (i *)
          loop
  loop
  readSTRef rr

fac :: Int -> Int
fac n = runST (facST n)

main :: IO ()
main = do
  print (fac 10)
