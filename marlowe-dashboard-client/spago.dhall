{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "marlowe-dashboard-client"
, dependencies =
  [ "aff-promise"
  , "avar"
  , "concurrent-queues"
  , "coroutines"
  , "debug"
  , "effect"
  , "filterable"
  , "formatters"
  , "halogen"
  , "markdown"
  , "node-fs"
  , "numerics"
  , "now"
  , "prelude"
  , "psci-support"
  , "remotedata"
  , "servant-support"
  , "test-unit"
  , "undefinable"
  , "unfoldable"
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
  ]
}
