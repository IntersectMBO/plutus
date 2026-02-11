letrec
  !revAppend : all a. list a -> list a -> list a
    = /\a ->
        \(l : list a) (r : list a) ->
          (let
              r = list a
            in
            \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z])
            r
            (\(x : a) (xs : list a) -> revAppend {a} xs (mkCons {a} x r))
            l
in
\(xs : list integer) -> revAppend {integer} xs xs