let
  data (Param :: * -> *) a | Param_match where
    Param : a -> Param a
  ~`$WParam` : all a. a -> Param a
    = /\a -> \(conrep : a) -> let !conrep : a = conrep in Param {a} conrep
  ~paramId : all a. Param a -> a -> a = /\a -> \(ds : Param a) (x : a) -> x
in
paramId {integer} (`$WParam` {integer} 1) 1