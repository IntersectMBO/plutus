module EmptyCase where

data Void

absurd1 :: Void -> a
absurd1 x = case x of {}

absurd2 :: Void -> a
absurd2 = \case {}

main :: IO ()
main = pure ()
