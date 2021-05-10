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
      https://github.com/purescript/package-sets/releases/download/psc-0.13.6-20200502/packages.dhall sha256:1e1ecbf222c709b76cc7e24cf63af3c2089ffd22bbb1e3379dfd3c07a1787694

let overrides =
      {- The package set we're using has `purescript-uuid` v6. This depends on the `uuid-validate` node
         module, which only works in node (it uses node's Buffer API). This was fine when we were using
         webpack 4, which provides polyfills for node stuff automatically. But webpack 5 - rightly, in
         my opinion - no longer provides these polyfills. I was going to add it back in manually when I
         noticed that the newer versions of `purescript-uuid` use the `uuid` node module, which works
         in the browser out of the box. :tada:
      -}
      { uuid =
          { dependencies = [ "effect", "maybe", "foreign-generic", "console", "spec" ]
          , repo = "https://github.com/spicydonuts/purescript-uuid.git"
          , version = "v8.0.0"
          }
      }

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
          , repo = "https://github.com/shmish111/purescript-servant-support"
          , version = "1805f896560751c48a04d3e29f9c109df850d8d3"
          }
      , concurrent-queues =
          { dependencies = [ "aff", "avar" ]
          , repo =
              "https://github.com/purescript-contrib/purescript-concurrent-queues.git"
          , version = "v1.1.0"
          }
        --   https://github.com/jmackie/purescript-datetime-iso/pull/11
      , datetime-iso =
          { dependencies = [ "newtype", "datetime", "parsing" ]
          , repo = "https://github.com/shmish111/purescript-datetime-iso"
          , version = "3a7cbe9fe22509393ddb6bd271f77c095326f6b3"
          }
      , foreign-generic =
            upstream.foreign-generic
          ⫽ { repo = "https://github.com/shmish111/purescript-foreign-generic"
            , version = "bd412a186bae788967cfc92fd3c5e1415355ff8c"
            }
      , matryoshka =
          { dependencies =
            [ "prelude", "fixed-points", "free", "transformers", "profunctor" ]
          , repo = "https://github.com/slamdata/purescript-matryoshka.git"
          , version = "v0.4.0"
          }
      , now =
          { dependencies =
              [ "console", "datetime", "effect", "psci-support" ]
          , repo = "https://github.com/purescript-contrib/purescript-now"
          , version = "v5.0.0"
          }
      , numerics =
          { dependencies =
            [ "prelude", "integers", "rationals", "uint", "bigints" ]
          , repo = "https://github.com/Proclivis/purescript-numerics"
          , version = "v0.1.2"
          }
      }

in  upstream ⫽ overrides ⫽ additions
