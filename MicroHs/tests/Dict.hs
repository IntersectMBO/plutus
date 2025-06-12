module Dict(module Dict) where
import Data.Constraint

fac :: forall a . (Num a, Eq a) => a -> a
fac n = if n == 0 then 1 else n * fac(n - 1)

facD :: forall a . Dict (Num a, Eq a) -> a -> a
facD Dict = fac

facDO :: forall a . Dict (Ord a, Num a) -> a -> a
facDO Dict = fac

dictInt :: Dict (Num Int, Eq Int)
dictInt = Dict

dictIntO :: Dict (Ord Int, Num Int)
dictIntO = Dict

main :: IO ()
main = do
  print $ facD dictInt 10
  print $ withDict dictInt (fac (11::Int))
  print $ facDO dictIntO 12
