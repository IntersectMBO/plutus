-- ill-typed. This fails at runtime since the builtin application is saturated.
(program 1.0.0 [(builtin addInteger) (con unit ()) (con integer 3)])