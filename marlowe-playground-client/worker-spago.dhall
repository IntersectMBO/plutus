{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "marlowe-playground-client-worker"
, dependencies =
    [ "bigints"
    , "console"
    , "debug"
    , "effect"
    , "foreign"
    , "foreign-generic"
    , "generics-rep"
    , "numerics"
    , "ordered-collections"
    , "parsing"
    , "prelude"
    , "profunctor-lenses"
    , "typelevel-prelude"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "worker/**/*.purs"
    , "src/Text/**/*.purs"
    , "src/Data/*.purs"
    , "src/Marlowe/Pretty.purs"
    , "src/Marlowe/Parser.purs"
    , "src/Marlowe/Holes.purs"
    , "src/Marlowe/Semantics.purs"
    , "src/Worker/Types.purs"
    , "generated/Examples/**/*.purs"
    ]
}
