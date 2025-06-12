module Forall where
-- Test nested forall in co-variant position

k :: forall a . a -> (forall b. b->b)
k _ y = y

a :: a -> (forall b . b)
a _ = undefined

type Memo a = forall r. (a -> r) -> (a -> r)

wrap :: (a -> b) -> (b -> a) -> Memo a -> Memo b
wrap i j m f = m (f . i) . j

main :: IO ()
main = print (k True 'a')
