{-
Welcome to your new Dhall package-set!

Below are instructions for how to edit this file for most use
cases, so that you don't need to know Dhall to use it.

## Warning: Don't Move This Top-Level Comment!

Due to how `dhall format` currently works, this comment's
instructions cannot appear near corresponding sections below
because `dhall format` will delete the comment. However,
it will not delete a top-level comment like this one.

## Use Cases

Most will want to do one or both of these options:
1. Override/Patch a package's dependency
2. Add a package not already in the default package set

This file will continue to work whether you use one or both options.
Instructions for each option are explained below.

### Overriding/Patching a package

Purpose:
- Change a package's dependency to a newer/older release than the
    default package set's release
- Use your own modified version of some dependency that may
    include new API, changed API, removed API by
    using your custom git repo of the library rather than
    the package set's repo

Syntax:
Replace the overrides' "{=}" (an empty record) with the following idea
The "//" or "⫽" means "merge these two records and
  when they have the same value, use the one on the right:"
-------------------------------
let override =
  { packageName =
      upstream.packageName // { updateEntity1 = "new value", updateEntity2 = "new value" }
  , packageName =
      upstream.packageName // { version = "v4.0.0" }
  , packageName =
      upstream.packageName // { repo = "https://www.example.com/path/to/new/repo.git" }
  }
-------------------------------

Example:
-------------------------------
let overrides =
  { halogen =
      upstream.halogen // { version = "master" }
  , halogen-vdom =
      upstream.halogen-vdom // { version = "v4.0.0" }
  }
-------------------------------

### Additions

Purpose:
- Add packages that aren't already included in the default package set

Syntax:
Replace the additions' "{=}" (an empty record) with the following idea:
-------------------------------
let additions =
  { package-name =
       { dependencies =
           [ "dependency1"
           , "dependency2"
           ]
       , repo =
           "https://example.com/path/to/git/repo.git"
       , version =
           "tag ('v4.0.0') or branch ('master')"
       }
  , package-name =
       { dependencies =
           [ "dependency1"
           , "dependency2"
           ]
       , repo =
           "https://example.com/path/to/git/repo.git"
       , version =
           "tag ('v4.0.0') or branch ('master')"
       }
  , etc.
  }
-------------------------------

Example:
-------------------------------
let additions =
  { benchotron =
      { dependencies =
          [ "arrays"
          , "exists"
          , "profunctor"
          , "strings"
          , "quickcheck"
          , "lcg"
          , "transformers"
          , "foldable-traversable"
          , "exceptions"
          , "node-fs"
          , "node-buffer"
          , "node-readline"
          , "datetime"
          , "now"
          ]
      , repo =
          "https://github.com/hdgarrood/purescript-benchotron.git"
      , version =
          "v7.0.0"
      }
  }
-------------------------------
-}


let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.13.3-20190920/packages.dhall sha256:53873cf2fc4a343a41f335ee47c1706ecf755ac7c5a336e8eb03ad23165dfd28

let overrides = {=}

let additions =
      { servant-support =
          { dependencies =
              [ "console"
              , "prelude"
              , "either"
              , "foldable-traversable"
              , "generics-rep"
              , "effect"
              , "aff"
              , "affjax"
              , "exceptions"
              , "web-xhr"
              , "foreign-generic"
              ]
          , repo =
              "https://github.com/shmish111/purescript-servant-support"
          , version =
              "purs-0.13"
          }
      , foreign-generic =
            upstream.foreign-generic
          ⫽ { repo =
                "https://github.com/shmish111/purescript-foreign-generic"
            , version =
                "purs-0.13"
            }
      , affjax =
          { dependencies =
              [ "aff"
              , "argonaut-core"
              , "arraybuffer-types"
              , "web-xhr"
              , "foreign"
              , "form-urlencoded"
              , "http-methods"
              , "integers"
              , "math"
              , "media-types"
              , "nullable"
              , "refs"
              , "unsafe-coerce"
              ]
          , repo =
              "https://github.com/krisajenkins/purescript-affjax"
          , version =
              "purs-0.13"
          }
      }

in  upstream ⫽ overrides ⫽ additions