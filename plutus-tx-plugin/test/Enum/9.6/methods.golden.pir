let
  !unitval : unit = ()
in
let
  !trace : all a. string -> a -> a = trace
in
let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
in
letrec
  data Unit | Unit_match where
    Unit : Unit
in
let
  ~traceError : all a. string -> a
    = /\a ->
        \(str : string) ->
          let
            !str : string = str
          in
          let
            !x : Unit = trace {Unit} str Unit
          in
          error {a} unitval
in
let
  ~toEnumBadArgumentError : string = "PT28"
in
let
  ~succBadArgumentError : string = "PT26"
in
let
  ~predBadArgumentError : string = "PT27"
in
let
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
in
let
  !ifThenElse : all a. bool -> a -> a -> a = ifThenElse
in
let
  !equalsInteger : integer -> integer -> bool = equalsInteger
in
let
  !addInteger : integer -> integer -> integer = addInteger
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  ~`$fEnumBool_$ctoEnum` : integer -> bool
    = \(lhs : integer) ->
        let
          !lhs : integer = lhs
        in
        ifThenElse
          {all dead. bool}
          (equalsInteger lhs 0)
          (/\dead -> False)
          (/\dead ->
             ifThenElse
               {all dead. bool}
               (equalsInteger lhs 1)
               (/\dead -> True)
               (/\dead -> traceError {bool} toEnumBadArgumentError)
               {all dead. dead})
          {all dead. dead}
in
let
  ~`$fEnumBool_$csucc` : bool -> bool
    = \(ds : bool) ->
        ifThenElse
          {all dead. bool}
          ds
          (/\dead -> traceError {bool} succBadArgumentError)
          (/\dead -> True)
          {all dead. dead}
in
let
  ~`$fEnumBool_$cpred` : bool -> bool
    = \(ds : bool) ->
        ifThenElse
          {all dead. bool}
          ds
          (/\dead -> False)
          (/\dead -> traceError {bool} predBadArgumentError)
          {all dead. dead}
in
let
  ~`$fEnumBool_$cfromEnum` : bool -> integer
    = \(ds : bool) -> ifThenElse {integer} ds 1 0
in
letrec
  ~`$dmenumFromTo_$cenumFromTo` : integer -> integer -> List integer
    = \(x : integer) (lim : integer) ->
        let
          !x : integer = x
        in
        let
          !lim : integer = lim
        in
        ifThenElse
          {all dead. List integer}
          (ifThenElse {bool} (lessThanEqualsInteger x lim) False True)
          (/\dead -> Nil {integer})
          (/\dead ->
             Cons
               {integer}
               x
               (`$dmenumFromTo_$cenumFromTo` (addInteger x 1) lim))
          {all dead. dead}
in
let
  ~`$fEnumBool_$cenumFromTo` : bool -> bool -> List bool
    = \(x : bool) (lim : bool) ->
        let
          !x : bool = x
        in
        let
          !lim : bool = lim
        in
        letrec
          ~go : List integer -> List bool
            = \(ds : List integer) ->
                List_match
                  {integer}
                  ds
                  {all dead. List bool}
                  (/\dead -> Nil {bool})
                  (\(x : integer) (xs : List integer) ->
                     /\dead -> Cons {bool} (`$fEnumBool_$ctoEnum` x) (go xs))
                  {all dead. dead}
        in
        go
          (`$dmenumFromTo_$cenumFromTo`
             (ifThenElse {integer} x 1 0)
             (ifThenElse {integer} lim 1 0))
in
`$fEnumBool_$cenumFromTo`
  (`$fEnumBool_$cpred` (`$fEnumBool_$csucc` False))
  (`$fEnumBool_$ctoEnum` (`$fEnumBool_$cfromEnum` True))