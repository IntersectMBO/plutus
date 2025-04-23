let
  ~`$fAdditiveMonoidInteger_$czero` : integer = 0
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  data (AdditiveMonoid :: * -> *) a | AdditiveMonoid_match where
    CConsAdditiveMonoid : (\a -> a -> a -> a) a -> a -> AdditiveMonoid a
  ~`$fAdditiveMonoidInteger` : AdditiveMonoid integer
    = CConsAdditiveMonoid {integer} addInteger `$fAdditiveMonoidInteger_$czero`
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  ~`$fFoldableList_$cfoldr` : all a b. (a -> b -> b) -> b -> List a -> b
    = /\a b ->
        \(f : a -> b -> b) ->
          let
            !f : a -> b -> b = f
          in
          \(z : b) ->
            let
              !z : b = z
            in
            letrec
              ~go : List a -> b
                = \(ds : List a) ->
                    List_match
                      {a}
                      ds
                      {all dead. b}
                      (/\dead -> z)
                      (\(x : a) (xs : List a) -> /\dead -> f x (go xs))
                      {all dead. dead}
            in
            \(eta : List a) -> go eta
  ~`$fFoldableList` :
     (\(t :: * -> *) -> all a b. (a -> b -> b) -> b -> t a -> b) List
    = `$fFoldableList_$cfoldr`
  ~build : all a. (all b. (a -> b -> b) -> b -> b) -> List a
    = /\a ->
        \(g : all b. (a -> b -> b) -> b -> b) ->
          g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a})
  ~`$p1AdditiveMonoid` : all a. AdditiveMonoid a -> (\a -> a -> a -> a) a
    = /\a ->
        \(v : AdditiveMonoid a) ->
          AdditiveMonoid_match
            {a}
            v
            {(\a -> a -> a -> a) a}
            (\(v : (\a -> a -> a -> a) a) (v : a) -> v)
  ~zero : all a. AdditiveMonoid a -> a
    = /\a ->
        \(v : AdditiveMonoid a) ->
          AdditiveMonoid_match
            {a}
            v
            {a}
            (\(v : (\a -> a -> a -> a) a) (v : a) -> v)
  ~sum :
     all (t :: * -> *) a.
       (\(t :: * -> *) -> all a b. (a -> b -> b) -> b -> t a -> b) t ->
       AdditiveMonoid a ->
       t a ->
       a
    = /\(t :: * -> *) a ->
        \(`$dFoldable` :
            (\(t :: * -> *) -> all a b. (a -> b -> b) -> b -> t a -> b) t)
         (`$dAdditiveMonoid` : AdditiveMonoid a) ->
          `$dFoldable`
            {a}
            {a}
            (`$p1AdditiveMonoid` {a} `$dAdditiveMonoid`)
            (zero {a} `$dAdditiveMonoid`)
in
sum
  {List}
  {integer}
  `$fFoldableList`
  `$fAdditiveMonoidInteger`
  (build
     {integer}
     (/\a -> \(c : integer -> a -> a) (n : a) -> c 1 (c 2 (c 3 (c 4 n)))))