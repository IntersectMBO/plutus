\(input : data) ->
  case
    integer
    (dropList {data} 3 (unListData input))
    [ (\(hd : data) (tl : list data) ->
         case
           integer
           (dropList {data} 3 tl)
           [ (\(hd : data) (tl : list data) ->
                case
                  integer
                  (dropList {data} 6 tl)
                  [ (\(hd : data) (tl : list data) ->
                       addInteger
                         (unIData hd)
                         (addInteger (unIData hd) (unIData hd))) ]) ]) ]