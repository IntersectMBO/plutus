module StandDer where

data X = X
deriving instance Show X

data T a = A | B | C a | D (T a)
deriving instance (Show a) => Show (T a)

newtype Y = Y X
deriving newtype instance Show Y

newtype M a = M (Maybe a)
  deriving Show
deriving newtype instance Functor M

newtype Z = Z X
  deriving Show

newtype YY = YY X
deriving via Z instance Show YY

main :: IO ()
main = do
  print X
  print [A, B, C True, D A]
  print (Y X)
  print (fmap fromEnum (M (Just 'a')))
  print (YY X)
