(program
   1.1.0
   ((\cse ->
       (\f ->
          (\z ->
             (\go eta -> go eta)
               ((\cse -> cse cse)
                  (\s ds -> case ds [z, (\x xs -> f x (s s xs))])))
            (case cse [(\v v -> v)]))
         (case cse [(\v v -> v)])
         (constr 1
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
                                                              [  ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]))
      (constr 0 [(\x y -> addInteger x y), 0])))