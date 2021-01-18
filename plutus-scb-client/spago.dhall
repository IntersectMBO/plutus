{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "plutus-scb-client"
, dependencies =
  [ "prelude"
  , "aff"
  , "avar"
  , "bigints"
  , "console"
  , "concurrent-queues"
  , "debug"
  , "effect"
  , "halogen"
  , "matryoshka"
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
  , "web-socket"
  ]
, packages = ./packages.dhall
, sources =
  [ "src/**/*.purs"
  , "test/**/*.purs"
  , "generated/**/*.purs"
  , "web-common/**/*.purs"
  , "web-common-plutus/**/*.purs"
  ]
}
