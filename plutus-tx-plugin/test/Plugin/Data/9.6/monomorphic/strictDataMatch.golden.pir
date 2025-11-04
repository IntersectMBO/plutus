let
  data (StrictTy :: * -> *) a | StrictTy_match where
    StrictTy : a -> a -> StrictTy a
  ~`$WStrictTy` : all a. a -> a -> StrictTy a
    = /\a ->
        \(conrep : a) ->
          let
            !conrep : a = conrep
          in
          \(conrep : a) ->
            let
              !conrep : a = conrep
            in
            StrictTy {a} conrep conrep
in
`$WStrictTy` {integer} 1 2