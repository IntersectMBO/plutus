module TypeApp where
import Data.Typeable

foo :: forall a b . (a, b)
foo = (undefined, undefined)

xread :: forall a -> Read a => String -> a
xread t s = read s :: t

main :: IO ()
main = do
  print $ read @Int "123"
  print $ xread Int "456"
  let (x, y) = foo @_ @Bool
  print $ typeOf y
  return @IO ()
