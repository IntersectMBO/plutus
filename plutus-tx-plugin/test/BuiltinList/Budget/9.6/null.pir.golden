let
  !null : all a. list a -> bool = nullList
  ~null : all a. list a -> bool
    = /\a -> \(l : list a) -> let !l : list a = l in null {a} l
  ~null : all a. list a -> bool = null
in
\(xs : list integer) -> let !xs : list integer = xs in null {integer} xs