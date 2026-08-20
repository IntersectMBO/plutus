let
  data MyEnum | MyEnum_match where
    Enum : MyEnum
    Enum : MyEnum
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~error : all a. unit -> a = /\a -> \(x : unit) -> error {a} unitval
in
\(ds : MyEnum) ->
  let
    !ds : MyEnum = ds
  in
  MyEnum_match
    ds
    {all dead. integer}
    (/\dead -> 1)
    (/\dead -> error {integer} ())
    {all dead. dead}