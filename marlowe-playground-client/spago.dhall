{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "marlowe-playground-client"
, dependencies =
  [ "aff-promise"
  , "avar"
  , "concurrent-queues"
  , "console"
  , "coroutines"
  , "datetime"
  , "datetime-iso"
  , "debug"
  , "effect"
  , "formatters"
  , "functions"
  , "halogen"
  , "matryoshka"
  , "node-fs"
  , "prelude"
  , "psci-support"
  , "routing"
  , "routing-duplex"
  , "remotedata"
  , "servant-support"
  , "simple-json"
  , "string-parsers"
  , "test-unit"
  , "undefinable"
  , "uuid"
  , "web-socket"
  ]
, packages = ./packages.dhall
, sources =
  [ "src/**/*.purs"
  , "test/**/*.purs"
  , "generated/**/*.purs"
  , "../web-common/**/*.purs"
  ]
}
