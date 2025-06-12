module Example where

fix :: forall a b. ((a -> b) -> a -> b) -> a -> b
fix f x = f (\v -> (funSafeCoerce x) x v) (funSafeCoerce (\v -> (funSafeCoerce x) x v))

funSafeCoerce :: forall a b . a -> b
funSafeCoerce = _primitive "I"

noMethodError :: forall a. [Char] -> a
noMethodError = funSafeCoerce ()

data Char = Char ()
fromString = const $ Char ()

infixr 0 $
($) :: forall a b . (a -> b) -> a -> b
($) f x = f x

const :: forall a b. a -> b -> b
const _ x = x

data Fun = Bob | Is | Having | Fun

data Number = Z | S Number

add :: Number -> Number -> Number
add = fix go
  where
    go r x y =
      case x of
        (S x') -> S $ r x' y
        Z -> y

class Foo a where
  foo :: a -> Number

instance Foo Number where
  foo = add Z

instance Foo () where
  foo () = Z

instance Foo Fun where
  foo Bob = Z
  foo Is = S Z
  foo Having = S $ S Z
  foo Fun = S $ S $ S Z

data Rob = Rob

instance Foo Rob where

main = foo @Rob
