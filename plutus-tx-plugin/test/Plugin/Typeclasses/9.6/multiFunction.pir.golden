let
  data Animal | Animal_match where
    Cat : Animal
    Dog : Animal
  data (PersonLike :: * -> *) a | PersonLike_match where
    CConsPersonLike : (a -> integer) -> (a -> Animal -> bool) -> PersonLike a
  ~age : all a. PersonLike a -> a -> integer
    = /\a ->
        \(v : PersonLike a) ->
          PersonLike_match
            {a}
            v
            {a -> integer}
            (\(v : a -> integer) (v : a -> Animal -> bool) -> v)
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~lessThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanInteger x y
  ~likesAnimal : all a. PersonLike a -> a -> Animal -> bool
    = /\a ->
        \(v : PersonLike a) ->
          PersonLike_match
            {a}
            v
            {a -> Animal -> bool}
            (\(v : a -> integer) (v : a -> Animal -> bool) -> v)
  ~predicate : all p. PersonLike p -> p -> bool
    = /\p ->
        \(`$dPersonLike` : PersonLike p) (p : p) ->
          let
            !p : p = p
          in
          case
            (all dead. bool)
            (likesAnimal {p} `$dPersonLike` p Cat)
            [ (/\dead -> False)
            , (/\dead -> lessThanInteger (age {p} `$dPersonLike` p) 30) ]
            {all dead. dead}
  data Person | Person_match where
    Jane : Person
    Jim : Person
  ~`$cage` : Person -> integer
    = \(ds : Person) -> Person_match ds {integer} 35 30
  ~`$clikesAnimal` : Person -> Animal -> bool
    = \(ds : Person) (ds : Animal) ->
        Person_match
          ds
          {all dead. bool}
          (/\dead -> Animal_match ds {bool} True False)
          (/\dead -> False)
          {all dead. dead}
  ~`$fPersonLikePerson` : PersonLike Person
    = CConsPersonLike {Person} `$cage` `$clikesAnimal`
in
\(ds : Person) ->
  let
    !ds : Person = ds
  in
  predicate {Person} `$fPersonLikePerson` ds