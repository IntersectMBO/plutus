-- ill-typed but does not fail at runtime because the builtin application is not saturated.
(program 1.0.0 [(builtin addInteger) (con unit ())])