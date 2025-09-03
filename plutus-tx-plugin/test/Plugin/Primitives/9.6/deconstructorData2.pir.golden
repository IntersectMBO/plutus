let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  ~`$fFunctorTuple2_$cfmap` : all c a b. (a -> b) -> Tuple2 c a -> Tuple2 c b
    = /\c a b ->
        \(f : a -> b) ->
          let
            !f : a -> b = f
          in
          \(ds : Tuple2 c a) ->
            Tuple2_match
              {c}
              {a}
              ds
              {Tuple2 c b}
              (\(c : c) (a : a) -> Tuple2 {c} {b} c (f a))
  ~`$fFunctorTuple2` :
     all c. (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) (Tuple2 c)
    = `$fFunctorTuple2_$cfmap`
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
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
  ~`$fFunctorList` : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) List
    = `$fFunctorList_$cfmap`
  ~`.` : all b c a. (b -> c) -> (a -> b) -> a -> c
    = /\b c a -> \(f : b -> c) (g : a -> b) (x : a) -> f (g x)
  ~fmap :
     all (f :: * -> *).
       (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f ->
       (all a b. (a -> b) -> f a -> f b)
    = /\(f :: * -> *) ->
        \(v : (\(f :: * -> *) -> all a b. (a -> b) -> f a -> f b) f) -> v
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
in
letrec
  ~matchData_go : list data -> List data
    = caseList'
        {data}
        {List data}
        (Nil {data})
        (\(x : data) ->
           let
             !x : data = x
           in
           \(xs : list data) ->
             let
               !xs : list data = xs
             in
             Cons {data} x (matchData_go xs))
in
let
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~unsafeDataAsConstr : data -> Tuple2 integer (List data)
    = \(d : data) ->
        let
          !d : data = d
          !p : pair integer (list data) = unsafeDataAsConstr d
        in
        casePair
          {integer}
          {list data}
          {Tuple2 integer (List data)}
          p
          (\(l : integer) ->
             let
               !l : integer = l
             in
             \(r : list data) ->
               let
                 !r : list data = r
               in
               Tuple2 {integer} {List data} l (matchData_go r))
  !unsafeDataAsI : data -> integer = unIData
  ~unsafeDataAsI : data -> integer
    = \(d : data) -> let !d : data = d in unsafeDataAsI d
in
\(ds : data) ->
  let
    !ds : data = ds
  in
  `.`
    {List data -> List integer}
    {Tuple2 integer (List data) -> Tuple2 integer (List integer)}
    {data -> integer}
    (fmap
       {Tuple2 integer}
       (`$fFunctorTuple2` {integer})
       {List data}
       {List integer})
    (fmap {List} `$fFunctorList` {data} {integer})
    unsafeDataAsI
    (unsafeDataAsConstr ds)