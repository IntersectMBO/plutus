module Lang where

import           Numeric.Natural (Natural)

data Exp a = Val Natural
           | Var a
           | Add (Exp a) (Exp a)
               deriving Show

eval :: (a -> Natural) -> Exp a -> Natural
eval η (Var x)     = η x
eval η (Val n)     = n
eval η (Add e1 e2) = eval η e1 + eval η e2

