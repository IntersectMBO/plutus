module Exists(main) where

data E = forall a . Show a => C a

es :: [E]
es = [C True, C 'a', wrap (C (1::Int))]

instance Show E where
  show (C a) = show a

wrap :: E -> E
wrap (C a) = C [a]

eio :: IO E
eio = return (C True)

someE :: E
someE = C (Just 'a')

foo :: E -> String
foo x | C a <- x = show a

bar :: E -> String
bar x =
  case x of
    C a -> show a

data T a = Show a => T a

sh :: forall a . T a -> String
sh (T a) = show a

data D = forall a . (Show a, Num a) => D a

unD :: D -> String
unD (D x) = show (x+1)

main :: IO ()
main = do
  print es
  C x <- eio
  print x
  putStrLn (foo someE)
  putStrLn (bar someE)
  putStrLn (sh (T True))
  putStrLn (sh (T 'x'))
  putStrLn (unD (D (1::Int)))
  putStrLn (unD (D 1.5))
