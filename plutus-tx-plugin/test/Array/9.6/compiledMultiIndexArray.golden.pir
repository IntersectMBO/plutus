(let
    !multiIndexArray : all a. array a -> list integer -> list a
      = multiIndexArray
  in
  multiIndexArray {data})
  (let
    !unitval : unit = ()
  in
  let
    !mkNilData : unit -> list data = mkNilData
  in
  let
    !mkI : integer -> data = iData
  in
  let
    !mkCons : all a. a -> list a -> list a = mkCons
  in
  let
    !listToArray : all a. list a -> array a = listToArray
  in
  listToArray
    {data}
    (mkCons
       {data}
       (mkI 1)
       (mkCons {data} (mkI 2) (mkCons {data} (mkI 3) (mkNilData unitval)))))
  [2,0,0,1]