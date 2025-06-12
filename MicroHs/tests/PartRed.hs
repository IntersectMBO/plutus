module PartRed where
import Primitives

k2 :: Int -> Int -> Int -> Int
k2 x y z = x

f2 :: Int -> Int
f2 = k2 1 2

k3 :: Int -> Int -> Int -> Int -> Int
k3 x y z w = x

f3 :: Int -> Int
f3 = k3 1 2 3

f32 :: Int -> Int -> Int
f32 = k3 1 2

k4 :: Int -> Int -> Int -> Int -> Int -> Int
k4 x y z w v = x

f4 :: Int -> Int
f4 = k4 1 2 3 4

f42 :: Int -> Int -> Int -> Int
f42 = k4 1 2

f43 :: Int -> Int -> Int
f43 = k4 1 2 3


-----

type S a = (a->a, a->a)

sInt :: S Int
sInt = (id, primIntNeg)

j :: S a -> (a -> a) -> a -> a
j d x y = snd d (x y)

k :: (Int -> Int) -> Int -> Int
k = j sInt

---

c'b :: (Int -> Int -> Int) -> (Int -> Int) -> Int -> Int -> Int
c'b x y z w = x z (y w)

fc'b :: Int -> Int
fc'b = c'b primIntAdd primIntNeg 99

---

cZ :: (Int -> Int) -> Int -> Int -> Int
cZ x y z = x y

fcZ :: Int -> Int
fcZ = cZ primIntNeg 11

---

r :: Int -> (Int -> Int -> Int) -> Int -> Int
r x y z = y z x

fr :: Int -> Int
fr = r 22 primIntQuot

main :: IO ()
main = do
  cprint k2
  cprint f2
  cprint k3
  cprint f3
  cprint f32
  cprint k4
  cprint f4
  cprint f42
  cprint f43
  --
  cprint k
  --
  cprint c'b
  cprint fc'b
  --
  cprint cZ
  cprint fcZ
  --
  cprint r
  cprint fr


-- R x y = C y x
