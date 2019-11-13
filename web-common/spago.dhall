{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name =
	"web-common"
, dependencies =
	[ "ace-halogen"
	, "console"
	, "effect"
	, "either"
	, "foreign-generic"
	, "halogen"
	, "maybe"
	, "prelude"
	, "profunctor-lenses"
	, "psci-support"
	, "remotedata"
	, "servant-support"
	, "transformers"
	, "undefinable"
	]
, packages =
	./packages.dhall
, sources =
	[ "src/**/*.purs", "test/**/*.purs" ]
}