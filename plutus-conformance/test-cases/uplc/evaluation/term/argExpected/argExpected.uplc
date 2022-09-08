-- addInteger is monomorphic so it must not be forced
(program 1.0.0 [(force (builtin addInteger)) (con integer 5) (con integer 6)])