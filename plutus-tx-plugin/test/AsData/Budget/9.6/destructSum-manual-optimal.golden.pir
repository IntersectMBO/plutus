let
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
in
\(d : data) ->
  let
    !constrPair : pair integer (list data) = unConstrData d
  in
  (let
      a = integer -> list data -> data
    in
    /\b -> \(f : a -> b) (x : a) -> f x)
    {data}
    ((let
         b = list data
       in
       /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
       {data}
       constrPair)
    (\(idx : integer) (args : list data) ->
       case
         data
         idx
         [ (headList {data} args)
         , (headList {data} args)
         , (let
           !intsB : list data
             = (let
                   a = pair integer (list data)
                 in
                 /\b -> \(f : a -> b) (x : a) -> f x)
                 {list data}
                 (snd {integer} {list data})
                 (unConstrData (headList {data} (tailList {data} args)))
           !intsA : list data
             = (let
                   a = pair integer (list data)
                 in
                 /\b -> \(f : a -> b) (x : a) -> f x)
                 {list data}
                 (snd {integer} {list data})
                 (unConstrData (headList {data} args))
           !b1_tail : list data = tailList {data} intsB
           !b : integer = unIData (headList {data} b1_tail)
           !b2_tail : list data = tailList {data} b1_tail
           !b : integer = unIData (headList {data} b2_tail)
           !b : integer
             = unIData
                 ((let
                      a = list data
                    in
                    /\b -> \(f : a -> b) (x : a) -> f x)
                    {data}
                    (headList {data})
                    (tailList {data} b2_tail))
           !b : integer = unIData (headList {data} intsB)
           !a1_tail : list data = tailList {data} intsA
           !a : integer = unIData (headList {data} a1_tail)
           !a2_tail : list data = tailList {data} a1_tail
           !a : integer = unIData (headList {data} a2_tail)
           !a : integer
             = unIData
                 ((let
                      a = list data
                    in
                    /\b -> \(f : a -> b) (x : a) -> f x)
                    {data}
                    (headList {data})
                    (tailList {data} a2_tail))
           !a : integer = unIData (headList {data} intsA)
         in
         (let
             a = list data
           in
           /\b -> \(f : a -> b) (x : a) -> f x)
           {data}
           (constrData 0)
           ((let
                a = list data
              in
              /\b -> \(f : a -> b) (x : a) -> f x)
              {list data}
              (mkCons {data} (iData (addInteger a b)))
              ((let
                   a = list data
                 in
                 /\b -> \(f : a -> b) (x : a) -> f x)
                 {list data}
                 (mkCons {data} (iData (addInteger a b)))
                 ((let
                      a = list data
                    in
                    /\b -> \(f : a -> b) (x : a) -> f x)
                    {list data}
                    (mkCons {data} (iData (addInteger a b)))
                    ((let
                         a = list data
                       in
                       /\b -> \(f : a -> b) (x : a) -> f x)
                       {list data}
                       (mkCons {data} (iData (addInteger a b)))
                       []))))) ])