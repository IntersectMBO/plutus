{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "marlowe-playground-client"
, dependencies =
    [ "ace"
    , "ace-halogen"
    , "bigints"
    , "console"
    , "debug"
    , "effect"
    , "functions"
    , "halogen"
    , "matryoshka"
    , "node-fs"
    , "numerics"
    , "string-parsers"
    , "prelude"
    , "psci-support"
    , "remotedata"
    , "servant-support"
    , "simple-json"
    , "web-socket"
    , "coroutines"
    , "aff-coroutines"
    , "test-unit"
    , "undefinable"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "src/**/*.purs"
    , "test/**/*.purs"
    , "generated/**/*.purs"
    , "../web-common/src/**/*.purs"
    , "../playground-common/src/**/*.purs"
    ]
}
