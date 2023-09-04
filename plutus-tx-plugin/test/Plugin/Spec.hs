module Plugin.Spec where

import Test.Tasty.Extras

import Plugin.Basic.Spec
import Plugin.Coverage.Spec
import Plugin.Data.Spec
import Plugin.Debug.Spec
import Plugin.Errors.Spec
import Plugin.Functions.Spec
import Plugin.Laziness.Spec
import Plugin.NoTrace.Spec
import Plugin.Optimization.Spec
import Plugin.Patterns.Spec
import Plugin.Primitives.Spec
import Plugin.Profiling.Spec
import Plugin.Strict.Spec
import Plugin.Typeclasses.Spec

tests :: TestNested
tests = testNested "Plugin" [
    basic
  , primitives
  , datat
  , debug
  , functions
  , laziness
  , noTrace
  , optimization
  , errors
  , typeclasses
  , strict
  , profiling
  , coverage
  , patterns
  ]
