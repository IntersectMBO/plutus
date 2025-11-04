let
  data MyEnum | MyEnum_match where
    Enum : MyEnum
    Enum : MyEnum
  data Unit | Unit_match where
    Unit : Unit
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~error : all a. Unit -> a = /\a -> \(x : Unit) -> error {a} unitval
in
\(ds : MyEnum) ->
  let
    !ds : MyEnum = ds
  in
  MyEnum_match
    ds
    {all dead. integer}
    (/\dead -> 1)
    (/\dead -> error {integer} Unit)
    {all dead. dead}