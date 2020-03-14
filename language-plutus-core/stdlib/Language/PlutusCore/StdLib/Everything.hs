-- | This module exports everything from the stdlib via a data type which allows to test
-- various procedures (pretty-printing, type checking, etc) over the entire stdlib in a
-- convenient way: each time a function / data type is added to the stdlib, none of the
-- tests is required to be adapted, instead you just add the new definition to 'stdLib'
-- defined below and all the tests see it automatically.

{-# LANGUAGE ScopedTypeVariables #-}

module Language.PlutusCore.StdLib.Everything
    ( stdLib
    ) where

import           Language.PlutusCore.FsTree
import           Language.PlutusCore.Universe

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function   as Function
import           Language.PlutusCore.StdLib.Data.Integer
import           Language.PlutusCore.StdLib.Data.List       as List
import           Language.PlutusCore.StdLib.Data.Nat        as Nat
import           Language.PlutusCore.StdLib.Data.Sum        as Sum
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type

-- | The entire stdlib exported as a single value.
stdLib :: PlcFolderContents DefaultUni
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
                  [ plcTermFile "SuccInteger" succInteger
                  ]
              , treeFolderContents "List"
                  [ plcTypeFile "List"       $ _recursiveType listData
                  , plcTermFile "Nil"        nil
                  , plcTermFile "Cons"       cons
                  , plcTermFile "FoldrList"  foldrList
                  , plcTermFile "FoldList"   foldList
                  , plcTermFile "Reverse"    List.reverse
                  , plcTermFile "EnumFromTo" List.enumFromTo
                  , plcTermFile "Sum"        List.sum
                  , plcTermFile "Product"    List.product
                  ]
              , treeFolderContents "Nat"
                  [ plcTypeFile "Nat"          $ _recursiveType natData
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
