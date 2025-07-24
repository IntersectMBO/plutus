let
  ~nandDirect : bool -> bool -> bool
    = \(ds : bool) ->
        let
          !ds : bool = ds
        in
        \(ds : bool) ->
          let
            !ds : bool = ds
          in
          case
            (all dead. bool)
            ds
            [(/\dead -> case bool ds [True, False]), (/\dead -> False)]
            {all dead. dead}
  ~andDirect : bool -> bool -> bool
    = \(ds : bool) ->
        let
          !ds : bool = ds
        in
        \(ds : bool) ->
          let
            !ds : bool = ds
          in
          nandDirect (nandDirect ds ds) (nandDirect ds ds)
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  ~allDirect : all a. (a -> bool) -> List a -> bool
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
          in
          \(l : List a) ->
            let
              !l : List a = l
            in
            List_match
              {a}
              l
              {bool}
              True
              (\(h : a) (t : List a) -> andDirect (p h) (allDirect {a} p t))
in
let
  ~build : all a. (all b. (a -> b -> b) -> b -> b) -> List a
    = /\a ->
        \(g : all b. (a -> b -> b) -> b -> b) ->
          g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a})
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~lessThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanInteger x y
in
allDirect
  {integer}
  (\(ds : integer) -> let !ds : integer = ds in lessThanInteger ds 5)
  (build {integer} (/\a -> \(c : integer -> a -> a) (n : a) -> c 7 (c 6 n)))