let
  ~v : integer = 1
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~`$fAdditiveSemigroupInteger` : (\a -> a -> a -> a) integer = addInteger
  ~`+` : all a. (\a -> a -> a -> a) a -> a -> a -> a
    = /\a -> \(v : (\a -> a -> a -> a) a) -> v
  ~v : integer -> integer -> integer
    = `+` {integer} `$fAdditiveSemigroupInteger`
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
  ~`$fFunctorList_$cfmap` : all a b. (a -> b) -> List a -> List b
    = /\a b ->
        \(f : a -> b) ->
          let
            !f : a -> b = f
          in
          letrec
            ~go : List a -> List b
              = \(ds : List a) ->
                  List_match
                    {a}
                    ds
                    {all dead. List b}
                    (/\dead -> Nil {b})
                    (\(x : a) (xs : List a) -> /\dead -> Cons {b} (f x) (go xs))
                    {all dead. dead}
          in
          \(eta : List a) -> go eta
  data (Applicative :: (* -> *) -> *) (f :: * -> *) | Applicative_match where
    CConsApplicative :
      (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f ->
      (all a. a -> f a) ->
      (all a b. f (a -> b) -> f a -> f b) ->
      Applicative f
  ~`$p1Applicative` :
     all (f :: * -> *).
       Applicative f -> (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f
    = /\(f :: * -> *) ->
        \(v : Applicative f) ->
          Applicative_match
            {f}
            v
            {(\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f}
            (\(v : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f)
              (v : all a. a -> f a)
              (v : all a b. f (a -> b) -> f a -> f b) ->
               v)
  ~`<*>` :
     all (f :: * -> *). Applicative f -> (all a b. f (a -> b) -> f a -> f b)
    = /\(f :: * -> *) ->
        \(v : Applicative f) ->
          Applicative_match
            {f}
            v
            {all a b. f (a -> b) -> f a -> f b}
            (\(v : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f)
              (v : all a. a -> f a)
              (v : all a b. f (a -> b) -> f a -> f b) ->
               v)
  ~pure : all (f :: * -> *). Applicative f -> (all a. a -> f a)
    = /\(f :: * -> *) ->
        \(v : Applicative f) ->
          Applicative_match
            {f}
            v
            {all a. a -> f a}
            (\(v : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f)
              (v : all a. a -> f a)
              (v : all a b. f (a -> b) -> f a -> f b) ->
               v)
  ~`$fTraversableList_$ctraverse` :
     all (f :: * -> *) a b. Applicative f -> (a -> f b) -> List a -> f (List b)
    = /\(f :: * -> *) a b ->
        \(`$dApplicative` : Applicative f) (f : a -> f b) ->
          let
            !f : a -> f b = f
          in
          letrec
            ~go : List a -> f (List b)
              = \(ds : List a) ->
                  List_match
                    {a}
                    ds
                    {all dead. f (List b)}
                    (/\dead -> pure {f} `$dApplicative` {List b} (Nil {b}))
                    (\(x : a) (xs : List a) ->
                       /\dead ->
                         let
                           !x : f b = f x
                         in
                         `<*>`
                           {f}
                           `$dApplicative`
                           {List b}
                           {List b}
                           (`$p1Applicative`
                              {f}
                              `$dApplicative`
                              {b}
                              {List b -> List b}
                              (\(ds : b) (ds : List b) -> Cons {b} ds ds)
                              x)
                           (go xs))
                    {all dead. dead}
          in
          \(eta : List a) -> go eta
  data (Traversable :: (* -> *) -> *) (t :: * -> *) | Traversable_match where
    CConsTraversable :
      (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) t ->
      (\(t :: * -> *) -> all a b. (a -> b -> b) -> b -> t a -> b) t ->
      (all (f :: * -> *) a b. Applicative f -> (a -> f b) -> t a -> f (t b)) ->
      Traversable t
  ~`$fTraversableList` : Traversable List
    = CConsTraversable
        {List}
        `$fFunctorList_$cfmap`
        `$fFoldableList_$cfoldr`
        `$fTraversableList_$ctraverse`
  ~build : all a. (all b. (a -> b -> b) -> b -> b) -> List a
    = /\a ->
        \(g : all b. (a -> b -> b) -> b -> b) ->
          g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a})
  ~`$fApplicativeIdentity_$cpure` : all a. a -> (\a -> a) a
    = /\a -> \(ds : a) -> ds
  ~id : all a. a -> a = /\a -> \(x : a) -> x
  ~`$fApplicativeIdentity` : Applicative (\a -> a)
    = CConsApplicative
        {\a -> a}
        (/\a b -> id {a -> b})
        `$fApplicativeIdentity_$cpure`
        (/\a b -> id {a -> b})
  ~traverse :
     all (t :: * -> *).
       Traversable t ->
       (all (f :: * -> *) a b. Applicative f -> (a -> f b) -> t a -> f (t b))
    = /\(t :: * -> *) ->
        \(v : Traversable t) ->
          Traversable_match
            {t}
            v
            {all (f :: * -> *) a b.
               Applicative f -> (a -> f b) -> t a -> f (t b)}
            (\(v : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) t)
              (v :
                 (\(t :: * -> *) -> all a b. (a -> b -> b) -> b -> t a -> b) t)
              (v :
                 all (f :: * -> *) a b.
                   Applicative f -> (a -> f b) -> t a -> f (t b)) ->
               v)
  ~fmapDefault : all (t :: * -> *) a b. Traversable t -> (a -> b) -> t a -> t b
    = /\(t :: * -> *) a b ->
        \(`$dTraversable` : Traversable t) ->
          traverse {t} `$dTraversable` {\a -> a} {a} {b} `$fApplicativeIdentity`
in
fmapDefault
  {List}
  {integer}
  {integer}
  `$fTraversableList`
  (\(v : integer) -> v v v)
  (build
     {integer}
     (/\a -> \(c : integer -> a -> a) (n : a) -> c 1 (c 2 (c 3 (c 4 n)))))