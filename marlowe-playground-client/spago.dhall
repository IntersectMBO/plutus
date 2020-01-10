{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "marlowe-playground-client"
, dependencies =
    [ "ace"
    , "ace-halogen"
    , "aff-coroutines"
    , "bigints"
    , "console"
    , "coroutines"
    , "debug"
    , "effect"
    , "functions"
    , "halogen"
    , "matryoshka"
    , "node-fs"
    , "numerics"
    , "parsing"
    , "prelude"
    , "psci-support"
    , "remotedata"
    , "servant-support"
    , "simple-json"
    , "test-unit"
    , "undefinable"
    , "web-socket"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "src/**/*.purs"
    , "test/**/*.purs"
    , "generated/**/*.purs"
    , "../web-common/src/**/*.purs"
    ]
}
