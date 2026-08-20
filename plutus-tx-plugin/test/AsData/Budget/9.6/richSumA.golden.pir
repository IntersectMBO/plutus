\(d : data) ->
  case
    integer
    d
    [ (\(args : list data) ->
         case
           integer
           args
           [ (\(hd : data) (tl : list data) ->
                case
                  integer
                  tl
                  [(\(hd : data) (tl : list data) -> unIData hd)]) ])
    , (\(args : list data) ->
         case
           integer
           (dropList {data} 2 args)
           [ (\(hd : data) (tl : list data) ->
                addInteger
                  (unIData hd)
                  (unIData (headList {data} (dropList {data} 3 tl)))) ])
    , (\(args : list data) ->
         case
           integer
           (dropList {data} 3 args)
           [ (\(hd : data) (tl : list data) ->
                case
                  integer
                  (dropList {data} 4 tl)
                  [ (\(hd : data) (tl : list data) ->
                       case
                         integer
                         (dropList {data} 4 tl)
                         [ (\(hd : data) (tl : list data) ->
                              addInteger
                                (unIData hd)
                                (addInteger
                                   (unIData hd)
                                   (unIData hd))) ]) ]) ]) ]