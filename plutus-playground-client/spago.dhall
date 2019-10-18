{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
    "plutus-playground-client"
, dependencies =
    [ "prelude"
    , "ace-halogen"
    , "ace"
    , "aff"
    , "bigints"
    , "console"
    , "debug"
    , "effect"
    , "halogen"
    , "matryoshka"
    , "node-fs"
    , "numerics"
    , "parsing"
    , "argonaut-codecs"
    , "foreign-generic"
    , "psci-support"
    , "remotedata"
    , "servant-support"
    , "test-unit"
    , "undefinable"
    ]
, packages =
    ./packages.dhall
, sources =
    [ "src/**/*.purs"
    , "test/**/*.purs"
    , "generated/**/*.purs"
    , "../web-common/**/*.purs"
    ]
}
