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



-- The Maybe type

data Maybe a = { Nothing | Just a }



-- The Either type

data Either a b = { Left a | Right b }



