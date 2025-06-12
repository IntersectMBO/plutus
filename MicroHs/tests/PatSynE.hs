module PatSynE(pattern Sing, pattern Sings, pattern Swap, pattern One, T(..,AA)) where

pattern Sing :: a -> [a]
pattern Sing a = [a]

pattern Sings :: a -> [a] -> [a]
pattern Sings a as <- as@[a]

pattern Swap :: a -> a -> [a]
pattern Swap a b = [b, a]

pattern One :: (Eq a, Num a) => a
pattern One = 1

data T = A deriving (Show)
pattern AA :: T
pattern AA = A
