letrec
  !take : all a. (\arep -> list arep) a -> integer -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (n : integer) (l : list a) ->
          case
            (all dead. list a)
            (lessThanEqualsInteger n 0)
            [ (/\dead ->
                 case
                   (list a)
                   l
                   [ (\(x : a) (xs : list a) ->
                        mkCons
                          {a}
                          x
                          (take {a} `$dMkNil` (subtractInteger n 1) xs))
                   , `$dMkNil` ])
            , (/\dead -> `$dMkNil`) ]
            {all dead. dead}
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(xs : list integer) ->
  case
    (Maybe integer)
    (take {integer} [] 1 xs)
    [ (\(x : integer) (xs : list integer) ->
         case
           (Maybe integer)
           xs
           [ (\(ds : integer) (ds : list integer) -> Nothing {integer})
           , (Just {integer} x) ])
    , (Nothing {integer}) ]