-- tail is partial like haskell's and blows up when given an empty list
(program 0.0.0 [(force (builtin tailList)) [(builtin mkNilData) (con unit ())]])