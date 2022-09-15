-- ill-typed. this does fail at runtime since the builtin application is not saturated.
(program 1.0.0 [(builtin addInteger) (con unit ()) (con integer 3)])