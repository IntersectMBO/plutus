-- | This module exports everything from the stdlib via a data type which allows to test
-- various procedures (pretty-printing, type checking, etc) over the entire stdlib in a
-- convenient way: each time a function / data type is added to the stdlib, none of the
-- tests is required to be adapted, instead you just add the new definition to 'stdLib'
-- defined below and all the tests see it automatically.

{-# LANGUAGE ScopedTypeVariables #-}

module PlutusCore.StdLib.Everything
    ( stdLib
    ) where

import           PlutusCore.Default
import           PlutusCore.FsTree

import           PlutusCore.StdLib.Data.Bool
import           PlutusCore.StdLib.Data.ChurchNat
import           PlutusCore.StdLib.Data.Data
import           PlutusCore.StdLib.Data.Function   as Function
import           PlutusCore.StdLib.Data.Integer
import           PlutusCore.StdLib.Data.List       as Builtin
import           PlutusCore.StdLib.Data.Nat        as Nat
import           PlutusCore.StdLib.Data.Pair       as Builtin
import           PlutusCore.StdLib.Data.ScottList  as Scott
import           PlutusCore.StdLib.Data.Sum        as Sum
import           PlutusCore.StdLib.Data.Unit
import           PlutusCore.StdLib.Meta.Data.Tuple
import           PlutusCore.StdLib.Type

-- | The entire stdlib exported as a single value.
stdLib :: PlcFolderContents DefaultUni DefaultFun
stdLib =
    FolderContents
      [ treeFolderContents "StdLib"
          [ treeFolderContents "Data"
              [ treeFolderContents "Bool"
                  [ plcTypeFile "Bool"       bool
                  , plcTermFile "True"       true
                  , plcTermFile "False"      false
                  , plcTermFile "IfThenElse" ifThenElse
                  ]
              , treeFolderContents "ChurchNat"
                  [ plcTypeFile "ChurchNat"  churchNat
                  , plcTermFile "ChurchZero" churchZero
                  , plcTermFile "ChurchSucc" churchSucc
                  ]
              , treeFolderContents "Function"
                  [ plcTermFile "Const"  Function.const
                  , plcTermFile "Apply"  applyFun
                  , plcTypeFile "Self"   $ _recursiveType selfData
                  , plcTermFile "Unroll" unroll
                  , plcTermFile "Fix"    fix
                  , plcTermFile "Fix2"   $ fixN 2 fixBy
                  ]
              , treeFolderContents "Integer"
                  [ plcTypeFile "integer"     integer
                  , plcTermFile "SuccInteger" succInteger
                  ]
              , treeFolderContents "Pair"
                  [ plcTypeFile "Pair"    pair
                  , plcTermFile "Fst"     Builtin.fstPair
                  , plcTermFile "Snd"     Builtin.sndPair
                  , plcTermFile "Uncurry" Builtin.uncurry
                  ]
              , treeFolderContents "List"
                  [ plcTypeFile "List"      list
                  , plcTermFile "CaseList"  Builtin.caseList
                  , plcTermFile "FoldrList" Builtin.foldrList
                  ]
              , treeFolderContents "Data"
                  [ plcTypeFile "Data"     dataTy
                  , plcTermFile "caseData" caseData
                  ]
              , treeFolderContents "ScottList"
                  [ plcTypeFile "List"       listTy
                  , plcTermFile "Nil"        nil
                  , plcTermFile "Cons"       cons
                  , plcTermFile "FoldrList"  Scott.foldrList
                  , plcTermFile "FoldList"   Scott.foldList
                  , plcTermFile "Reverse"    Scott.reverse
                  , plcTermFile "EnumFromTo" Scott.enumFromTo
                  , plcTermFile "Sum"        Scott.sum
                  , plcTermFile "Product"    Scott.product
                  ]
              , treeFolderContents "Nat"
                  [ plcTypeFile "Nat"          natTy
                  , plcTermFile "Zero"         zero
                  , plcTermFile "Succ"         Nat.succ
                  , plcTermFile "FoldrNat"     foldrNat
                  , plcTermFile "FoldNat"      foldNat
                  , plcTermFile "NatToInteger" natToInteger
                  ]
              , treeFolderContents "Sum"
                  [ plcTypeFile "Sum"   Sum.sum
                  , plcTermFile "Left"  left
                  , plcTermFile "Right" right
                  ]
              , treeFolderContents "Unit"
                  [ plcTypeFile "Unit"    unit
                  , plcTermFile "Unitval" unitval
                  ]
              ]
          , treeFolderContents "Meta"
              [ treeFolderContents "Data"
                  [ treeFolderContents "Tuple"
                      [ plcTypeFile "ProdN2"   $ prodN 2
                      , plcTermFile "ProdN2_0" $ prodNAccessor 2 0
                      , plcTermFile "ProdN2_1" $ prodNAccessor 2 1
                      , plcTermFile "MkProdN2" $ prodNConstructor 2
                      ]
                  ]
              ]
          ]
      ]
