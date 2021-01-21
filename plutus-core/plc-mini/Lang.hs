module Lang where

import           Numeric.Natural (Natural)

data Exp = Val Natural
         | Add Exp Exp
             deriving Show

eval :: Exp -> Natural
eval (Val n)     = n
eval (Add e1 e2) = eval e1 + eval e2

