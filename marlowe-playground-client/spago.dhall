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
  , "decimals"
  , "effect"
  , "filterable"
  , "formatters"
  , "functions"
  , "halogen"
  , "matryoshka"
  , "node-fs"
  , "prelude"
  , "psci-support"
  , "remotedata"
  , "routing"
  , "routing-duplex"
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
  , "web-common/**/*.purs"
  , "web-common-marlowe/**/*.purs"
  , "web-common-playground/**/*.purs"
  ]
}
