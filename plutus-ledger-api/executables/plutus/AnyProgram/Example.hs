{-# LANGUAGE ImpredicativeTypes #-}

module AnyProgram.Example
  ( termExamples
  , typeExamples
  ) where

import Types

import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.StdLib.Data.Bool qualified as StdLib
import PlutusCore.StdLib.Data.ChurchNat qualified as StdLib
import PlutusCore.StdLib.Data.Integer qualified as StdLib
import PlutusCore.StdLib.Data.Unit qualified as StdLib

-- MAYBE: port also getInterestingExamples

-- TODO: generalize annotation after removal of Provenance
-- TODO: had to constrain it to Name&TyName, use sth like plcViaName to overcome this
termExamples
  :: [ ( ExampleName
       , forall term. TermLike term PLC.TyName PLC.Name DefaultUni DefaultFun => term ()
       )
     ]
termExamples =
  [ ("succInteger", StdLib.succInteger)
  , ("unitval", StdLib.unitval)
  , ("true", StdLib.true)
  , ("false", StdLib.false)
  , ("churchZero", StdLib.churchZero)
  , ("churchSucc", StdLib.churchSucc)
  ]

-- TODO: generalize annotation after removal of Provenance
-- TODO: had to constrain it to TyName, use sth like plcViaName to overcome this
typeExamples :: [(ExampleName, PLC.Type PLC.TyName DefaultUni ())]
typeExamples =
  [ ("unit", StdLib.unit)
  , ("churchNat", StdLib.churchNat)
  , ("bool", StdLib.bool)
  ]
