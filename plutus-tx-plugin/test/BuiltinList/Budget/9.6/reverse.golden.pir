let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
in
letrec
  ~revAppend : all a. list a -> list a -> list a
    = /\a ->
        \(l : list a) ->
          let
            !l : list a = l
          in
          \(r : list a) ->
            let
              !r : list a = r
            in
            caseList'
              {a}
              {list a}
              r
              (\(x : a) ->
                 let
                   !x : a = x
                 in
                 \(xs : list a) ->
                   let
                     !xs : list a = xs
                   in
                   revAppend {a} xs (mkCons {a} x r))
              l
in
let
  ~reverse : all a. (\arep -> list arep) a -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (xs : list a) ->
          let
            !xs : list a = xs
          in
          revAppend {a} xs `$dMkNil`
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  reverse {integer} `$fMkNilInteger` xs