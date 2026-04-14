(program
   1.1.0
   ((\s ->
       case
         (constr 0
            [ s
            , 0
            , (constr 1
                 [ 1
                 , (constr 1
                      [ 2
                      , (constr 1
                           [ 3
                           , (constr 1
                                [ 4
                                , (constr 1
                                     [ 5
                                     , (constr 1
                                          [ 6
                                          , (constr 1
                                               [ 7
                                               , (constr 1
                                                    [ 8
                                                    , (constr 1
                                                         [ 9
                                                         , (constr 1
                                                              [ 10
                                                              , (constr 0
                                                                   [  ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ])
         [s])
      (\s i ds ->
         case
           ds
           [ (constr 1 [])
           , (\x xs ->
                case
                  (lessThanEqualsInteger 10 x)
                  [ (constr 0 [i])
                  , ((\x -> case (constr 0 [s, x, xs]) [s])
                       (addInteger 1 i)) ]) ])))