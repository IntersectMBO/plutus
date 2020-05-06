{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "plutus-scb-client"
, dependencies =
  [ "prelude"
  , "aff"
  , "console"
  , "debug"
  , "effect"
  , "halogen"
  , "node-fs"
  , "argonaut-codecs"
  , "foreign-generic"
  , "psci-support"
  , "transformers"
  , "remotedata"
  , "servant-support"
  , "test-unit"
  , "undefinable"
  , "uuid"
  , "newtype"
  ]
, packages = ./packages.dhall
, sources =
  [ "src/**/*.purs"
  , "test/**/*.purs"
  , "generated/**/*.purs"
  , "../web-common/**/*.purs"
  ]
}
