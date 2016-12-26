-- The Unit type

data Unit = { MkUnit }



-- The Pair type

data Pair a b = { MkPair a b }

fst : forall a b. Pair a b -> a {
  fst (MkPair x _) = x
}

snd : forall a b. Pair a b -> b {
  snd (MkPair _ y) = y
}



-- The Bool type

data Bool = { True | False }

and : Bool -> Bool -> Bool {
  and True True = True ;
  and _ _ = False
}

or : Bool -> Bool -> Bool {
  or False False = False ;
  or _ _ = True
}

not : Bool -> Bool {
  not True = False ;
  not False = True
}



-- The List type

data List a = { Nil | Cons a (List a) }

length : forall a. List a -> Int {
  length Nil = 0 ;
  length (Cons _ xs) = !addInt 1 (length xs)
}

map : forall a b. (a -> b) -> List a -> List b {
  map _ Nil = Nil ;
  map f (Cons x xs) = Cons (f x) (map f xs)
}

filter : forall a. (a -> Bool) -> List a -> List a {
  filter _ Nil = Nil ;
  filter p (Cons x xs) =
    case p x of {
      False -> filter p xs ;
      True -> Cons x (filter p xs)
    }
}

zipWith : forall a b c. (a -> b -> c) -> List a -> List b -> List c {
  zipWith _ Nil _ = Nil ;
  zipWith _ _ Nil = Nil ;
  zipWith f (Cons x xs) (Cons y ys) =
    Cons (f x y) (zipWith f xs ys)
}

andList : List Bool -> Bool {
  andList Nil = True ;
  andList (Cons b bs) = and b (andList bs)
}

orList : List Bool -> Bool {
  orList Nil = False ;
  orList (Cons b bs) = or b (orList bs)
}



-- The Maybe type

data Maybe a = { Nothing | Just a }

catMaybe : forall a. List (Maybe a) -> List a {
  catMaybe Nil = Nil ;
  catMaybe (Cons Nothing xs) = catMaybe xs ;
  catMaybe (Cons (Just x) xs) = Cons x (catMaybe xs)
}



-- The Either type

data Either a b = { Left a | Right b }



-- Some Int builtins

lessThanEqualsInt : Int -> Int -> Bool {
  lessThanEqualsInt x y = not (!lessThanInt y x)
}



-- Some Float builtins

lessThanEqualsFloat : Float -> Float -> Bool {
  lessThanEqualsFloat x y = not (!lessThanFloat y x)
}




-- Multisig verification

verify : ByteString -> ByteString -> Maybe ByteString -> Bool {
  verify _ _ Nothing = False ;
  verify dat k (Just s) = !verifySignature k dat s
}

verifyMultiSig : Int -> List ByteString -> ByteString -> List (Maybe ByteString) -> Comp Unit {
  verifyMultiSig n keys dat sigs =
    case and (!equalsInt (length keys) (length sigs))
              (lessThanEqualsInt n (length (filter (\x -> x) (zipWith (verify dat) keys sigs)))) of {
      True -> success MkUnit ;
      False -> failure
    }
}