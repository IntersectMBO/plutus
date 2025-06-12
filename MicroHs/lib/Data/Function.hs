-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Function(module Data.Function) where
import Data.Bool_Type
import Prelude qualified ()
import Primitives
--import Data.Tuple

infixr 0 $
($) :: forall a b . (a -> b) -> a -> b
($) f x = f x

infixr 0 $!
($!) :: forall a b . (a -> b) -> a -> b
($!) f x = x `primSeq` f x

infixr 9 .
(.) :: forall a b c . (b -> c) -> (a -> b) -> (a -> c)
(.) f g x = f (g x)

id :: forall a . a -> a
id x = x

const :: forall a b . a -> b -> a
const x _ = x

flip :: forall a b c . (b -> a -> c) -> a -> b -> c
flip f a b = f b a

fix :: forall a . (a -> a) -> a
fix = primFix

infixl 0 `on`
on :: forall a b c . (a -> a -> b) -> (c -> a) -> (c -> c -> b)
on op sel x y = op (sel x) (sel y)

asTypeOf :: forall a . a -> a -> a
asTypeOf = const

seq :: forall a b . a -> b -> b
seq = primSeq

until :: forall a . (a -> Bool) -> (a -> a) -> a -> a
until p f = rec
  where
    rec x = if p x then x else rec (f x)

infixl 1 &
(&) :: forall a b . a -> (a -> b) -> b
(&) x f = f x

applyWhen :: forall a . Bool -> (a -> a) -> a -> a
applyWhen True  f x = f x
applyWhen False _ x = x
