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

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Integer
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type

-- | The entire stdlib exported as a single value.
stdLib :: PlcFolderContents
stdLib =
    FolderContents
      [ treeFolderContents "StdLib"
          [ treeFolderContents "Data"
              [ treeFolderContents "Bool"
                  [ plcTypeFile "Bool"  getBuiltinBool
                  , plcTermFile "True"  getBuiltinTrue
                  , plcTermFile "False" getBuiltinFalse
                  , plcTermFile "If"    getBuiltinIf
                  ]
              , treeFolderContents "ChurchNat"
                  [ plcTypeFile "ChurchNat"  getBuiltinChurchNat
                  , plcTermFile "ChurchZero" getBuiltinChurchZero
                  , plcTermFile "ChurchSucc" getBuiltinChurchSucc
                  ]
              , treeFolderContents "Function"
                  [ plcTermFile "Const"  getBuiltinConst
                  , plcTypeFile "Self"   $ _recursiveType <$> getBuiltinSelf
                  , plcTermFile "Unroll" getBuiltinUnroll
                  , plcTermFile "Fix"    getBuiltinFix
                  , plcTermFile "Fix2"   $ getBuiltinFixN 2
                  ]
              , treeFolderContents "Integer"
                  [ plcTermFile "SuccInteger" getBuiltinSuccInteger
                  ]
              , treeFolderContents "List"
                  [ plcTypeFile "List"       $ _recursiveType <$> getBuiltinList
                  , plcTermFile "Nil"        getBuiltinNil
                  , plcTermFile "Cons"       getBuiltinCons
                  , plcTermFile "FoldrList"  getBuiltinFoldrList
                  , plcTermFile "FoldList"   getBuiltinFoldList
                  , plcTermFile "EnumFromTo" getBuiltinEnumFromTo
                  , plcTermFile "Sum"        getBuiltinSum
                  , plcTermFile "Product"    getBuiltinProduct
                  ]
              , treeFolderContents "Nat"
                  [ plcTypeFile "Nat"          $ _recursiveType <$> getBuiltinNat
                  , plcTermFile "Zero"         getBuiltinZero
                  , plcTermFile "Succ"         getBuiltinSucc
                  , plcTermFile "FoldrNat"     getBuiltinFoldrNat
                  , plcTermFile "FoldNat"      getBuiltinFoldNat
                  , plcTermFile "NatToInteger" getBuiltinNatToInteger
                  ]
              , treeFolderContents "Unit"
                  [ plcTypeFile "Unit"    getBuiltinUnit
                  , plcTermFile "Unitval" getBuiltinUnitval
                  ]
              ]
          , treeFolderContents "Meta"
              [ treeFolderContents "Data"
                  [ treeFolderContents "Tuple"
                      [ plcTypeFile "ProdN2"   $ getBuiltinProdN 2
                      , plcTermFile "ProdN2_0" $ getBuiltinProdNAccessor 2 0
                      , plcTermFile "ProdN2_1" $ getBuiltinProdNAccessor 2 1
                      , plcTermFile "MkProdN2" $ getBuiltinProdNConstructor 2
                      ]
                  ]
              ]
          ]
      ]
