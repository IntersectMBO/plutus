let
  data Bool | Bool_match where
    True : Bool
    False : Bool
  data Unit | Unit_match where
    Unit : Unit
in
\(v : list integer) ->
  let
    !l : list integer = dropList {integer} 20 v
  in
  (let
      r = Unit -> Unit -> integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      chooseList
        {integer}
        {all dead. r}
        xs
        (/\dead -> z)
        (/\dead -> f (headList {integer} xs) (tailList {integer} xs))
        {r})
    (\(_ann : Unit) ->
       let
         !x : Unit = trace {Unit} "PT22" Unit
       in
       error {Unit -> integer})
    (\(x : integer) (xs : list integer) (ds : Unit) (eta : Unit) -> x)
    l
    Unit
    Unit