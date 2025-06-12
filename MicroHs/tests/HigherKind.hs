module HigherKind(main) where

newtype T f = C (f Int)

showT :: forall f . (f Int -> String) -> T f -> String
showT f (C x) = "(C " ++ f x ++ ")"

newtype TT f a = CC (f a)

showTT :: forall f a . (f a -> String) -> TT f a -> String
showTT f (CC x) = "(CC " ++ f x ++ ")"

type H :: (Type -> Type) -> Type
data H a = H

type HH :: forall (k::Kind) . k -> Type
data HH a = HH

hh1 :: HH Int
hh1 = HH
hh2 :: HH []
hh2 = HH

type List = []

tt :: TT List Int
tt = CC [1]

x :: Int
x =
  let h :: H []
      h = H
  in  1

showLI :: [Int] -> String
showLI = show

main :: IO ()
main = do
  let t = C [1]
  putStrLn $ showT  showLI t
  putStrLn $ showTT showLI tt
