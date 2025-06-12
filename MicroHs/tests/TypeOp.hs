module TypeOp where
import Data.Coerce

data a + b = Plus a b
type Foo = Int + Bool

x :: Int `Either` Bool
x = Left 5

type a ~~ b = Coercible a b

class a ~~ b => TypeOp a b

instance a ~~ b => TypeOp a b

f :: a ~~ b => a -> b
f = coerce

main :: IO ()
main = print (f x :: Either Int Bool)
