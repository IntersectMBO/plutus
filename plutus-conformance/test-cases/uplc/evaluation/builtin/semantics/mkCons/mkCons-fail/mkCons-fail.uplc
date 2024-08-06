-- a type mismatch
-- plutus implementation detail: note that this conceptually should be a machine type mismatch error (unlifting error),
-- but is currently a user evaluation failure, see: https://github.com/IntersectMBO/plutus/pull/3035
(program 1.0.0 [(force (builtin mkCons)) (con integer 3) [(builtin mkNilData) (con unit ())]])