module Irref where

data T = T Int Bool
newtype N = N Int
data M = C1 | C2 | C3 Int

irref :: Monad m => m ()
irref = do
  _ <- pure ()
  x1 <- pure ()
  (x2,x3) <- pure (1,2)
  (x4::Int) <- pure 1
  x5@(x6,x7) <- pure (1,2)
  !x8 <- pure 1
  ~[x9] <- pure []
  (id -> ()) <- pure ()
  N x10 <- pure (N 1)
  T x11 x12 <- pure (T 1 True)
  pure ()

ref1 :: MonadFail m => m ()
ref1 = do
  1 <- pure 2
  return ()

ref2 :: MonadFail m => m ()
ref2 = do
  (x, [y]) <- pure (1, [])
  return ()

ref3 :: MonadFail m => m ()
ref3 = do
  C1 <- pure C2
  return ()

ref4 :: MonadFail m => m ()
ref4 = do
  C3 _ <- pure C2
  return ()

pr :: Maybe () -> IO ()
pr = print

main :: IO ()
main = do
  ir <- irref
  print ir
  pr ref1
  pr ref2
  pr ref3
  pr ref4
