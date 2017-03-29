data Bool = { True | False }

not : Bool -> Bool {
  not True = False ;
  not False = True
}

data Nat = { Zero | Suc Nat }

even : Nat -> Bool {
  even Zero = True ;
  even (Suc Zero) = False ;
  even (Suc (Suc n)) = even n
}


plus : Nat -> Nat -> Nat {
  plus Zero y = y ;
  plus (Suc x) y = Suc (plus x y)
}

times : Nat -> Nat -> Nat {
  times Zero y = Zero ;
  times (Suc x) y = plus y (times x y)
}

fac : Nat -> Nat {
  fac Zero = Suc Zero ;
  fac (Suc n) = times (Suc n) (fac n)
}

data Unit = { Unit }

data List a = { Nil | Cons a (List a) }

map : forall a b. (a -> b) -> List a -> List b {
  map f Nil = Nil ;
  map f (Cons x xs) = Cons (f x) (map f xs)
}

doit : (forall a. a -> a) -> Int -> Int {
  doit f x = f x
}

{-
localTest : Nat -> Nat {
  localTest x =
    let { locid : Unit -> Nat -> Nat { locid z y = x } }
    in locid Unit Zero
}

validator : Comp Int -> Comp Int {
  validator x = x
}

x : Int -> Int {
  x i = i
}
-}