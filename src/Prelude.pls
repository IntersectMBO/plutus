-- The Unit type

data Unit = { MkUnit }



-- The Pair type

data Pair a b = { MkPair a b }



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



-- The Either type

data Either a b = { Left a | Right b }



-- Multisig verification

lengthBool : List Bool -> Int {
  lengthBool Nil = 0 ;
  lengthBool (Cons _ xs) = !addInt 1 (lengthBool xs)
}

lengthKeys : List ByteString -> Int {
  lengthKeys Nil = 0 ;
  lengthKeys (Cons _ xs) = !addInt 1 (lengthKeys xs)
}

lengthSignatures : List (Maybe ByteString) -> Int {
  lengthSignatures Nil = 0 ;
  lengthSignatures (Cons _ xs) = !addInt 1 (lengthSignatures xs)
}

catMaybeByteString : List (Maybe ByteString) -> List ByteString {
  catMaybeByteString Nil = Nil ;
  catMaybeByteString (Cons Nothing xs) = catMaybeByteString xs ;
  catMaybeByteString (Cons (Just x) xs) = Cons x (catMaybeByteString xs)
}

verify : ByteString -> ByteString -> Maybe ByteString -> Bool {
  verify _ _ Nothing = True ;
  verify dat k (Just s) = !verifySignature k dat s
}

zipWithVerify : ByteString -> List ByteString -> List (Maybe ByteString) -> List Bool {
  zipWithVerify _ Nil _ = Nil ;
  zipWithVerify _ _ Nil = Nil ;
  zipWithVerify dat (Cons k ks) (Cons ms mss) =
    Cons (verify dat k ms) (zipWithVerify dat ks mss)
}

filterBool : (Bool -> Bool) -> List Bool -> List Bool {
  filterBool _ Nil = Nil ;
  filterBool p (Cons b bs) =
    case p b of {
      True -> Cons b (filterBool p bs) ;
      False -> filterBool p bs
    }
}

verifyMultiSig : Int -> List ByteString -> ByteString -> List (Maybe ByteString) -> Comp Unit {
  verifyMultiSig n keys dat sigs =
    case and (!equalsInt (lengthKeys keys) (lengthSignatures sigs))
              (!lessThanInt n (lengthBool (filterBool (\x -> x) (zipWithVerify dat keys sigs)))) of {
      True -> success MkUnit ;
      False -> failure
    }
}