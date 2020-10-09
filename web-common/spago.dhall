{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "web-common"
, dependencies =
  [ "affjax"
  , "debug"
  , "foreign-generic"
  , "halogen"
  , "matryoshka"
  , "prelude"
  , "profunctor-lenses"
  , "servant-support"
  , "bigints"
  , "test-unit"
  , "undefinable"
  , "remotedata"
  , "web-socket"
  , "concurrent-queues"
  , "uuid"
  ]
, packages = ./packages.dhall
, sources =
  [ "src/**/*.purs", "../plutus-playground-client/generated/**/*.purs" ]
}
