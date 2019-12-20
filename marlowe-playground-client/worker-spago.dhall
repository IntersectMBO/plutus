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
    , "prelude"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "worker/**/*.purs"
    ]
}
