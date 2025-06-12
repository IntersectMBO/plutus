module Record(main) where

-- HasField instances are derived automatically

data R = CR { a :: Int, b :: Bool }

instance Show R where
  show (CR a b) = "CR{a=" ++ show a ++ ",b=" ++ show b ++ "}"

data RR = CRR { r :: R, a :: Bool }

instance Show RR where
  show (CRR r a) = "CRR{r=" ++ show r ++ ",a=" ++ show a ++ "}"

foo :: R -> Int
foo CR{a=aa,b=bb} = if bb then 999 else aa

foop :: R -> Int
foop CR{a,b} = if b then 888 else a

foow :: R -> Int
foow CR{..} = if b then 777 else a

bar :: R -> Int
bar CR{a=aa} = aa

r1 :: R
r1 = CR { a=1, b=True }

r2 :: R
r2 = CR { b=False, a=2 }

r3 :: R
r3 = CR { b=True }

--r4 :: R
--r4 = R { c=True }

r5 :: R
r5 = r1 { a = (10::Int) }

r6 :: R
r6 = r1 { a = (10::Int), b=False }

rr1 :: RR
rr1 = CRR { r = r1, a = True }

r7 :: RR
r7 = rr1{ r.a = 999 }

r8 :: R
r8 =
  let a = 333
      b = True
  in  CR{..}

sel_a :: forall r t . HasField "a" r t => r -> t
sel_a = (.a)

{- does not work yet
sel_ra :: RR -> Int
sel_ra CRR{r.a} = a
-}

data S a = S1 { x :: Int } | S2 { x :: Int, y :: a }

instance forall a . Show a => Show (S a) where
  show (S1 x) = "S1 " ++ show x
  show (S2 x y) = "S2 " ++ show x ++ " " ++ show y

s1 :: S Bool
s1 = S1 10

s2 :: S String
s2 = S2 { x = 20, y = "foo" }

main :: IO ()
main = do
  print r1
  print r2
--  print r3
  print r5
  print r6
  print r7
  print $ r2.a
  print $ r2.b
  print $ rr1.r.a
  print $ (.r.a) rr1
  print $ rr1.a
  print $ (.a) r1
  print $ sel_a r1
  print $ sel_a rr1
  print s1
  print s2
  print s1{x=99}
  print s2{x=88}
  print s2{y="bar"}
  print $ foo r1
  print $ foo r2
  print $ bar r1
  print $ foop r1
  print $ foop r2
  print $ foow r1
  print $ foow r2
--  print $ sel_ra r7
  print r8
  print s1.x
  print s2.x
  print (x s1)
  print (x s2)
