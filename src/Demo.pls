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

localTest : Nat -> Nat {
  localTest x =
    let { locid : Unit -> Nat -> Nat { locid z y = x } }
    in locid Unit Zero
}