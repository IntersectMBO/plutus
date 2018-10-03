-- | This module exports everything from the stdlib via a data type which allows to test
-- various procedures (pretty-printing, type checking, etc) over the entire stdlib in a
-- convenient way: each time a function / data type is added to the stdlib, none of the
-- tests is required to be adapted, instead you just add the new definition to 'stdLib'
-- defined below and all the tests see it automatically.

{-# LANGUAGE ScopedTypeVariables #-}

module Language.PlutusCore.StdLib.Everything
    ( foldStdLib
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit

-- We use 'String's for names, because this module exists for tests right now and
-- there we have 'FilePath's which are 'String's.

data Named a = Named String a

-- | A PLC entity in the standard library.
data AnonStdLibPlcEntity
    = AnonStdLibType (Quote (Type TyName ()))       -- ^ A type.
    | AnonStdLibTerm (Quote (Term TyName Name ()))  -- ^ A term.

type StdLibPlcEntity = Named AnonStdLibPlcEntity

-- | The contents of a file system entity in the standard library.
data AnonStdLibFsEntity
    = AnonStdLibFolder [StdLibFsEntity]   -- ^ A subfolder.
    | AnonStdLibFile   [StdLibPlcEntity]  -- ^ A file in the folder.

-- | A folder in the standard library.
type StdLibFsEntity = Named AnonStdLibFsEntity

-- | Fold a 'StdLibPlcEntity'.
foldStdLibPlcEntity
    :: (String -> Quote (Type TyName ())      -> a)  -- ^ What to do on a type.
    -> (String -> Quote (Term TyName Name ()) -> a)  -- ^ What to do on a term.
    -> StdLibPlcEntity
    -> a
foldStdLibPlcEntity onType onTerm (Named plcName anonStdLibPlcEntity) =
    case anonStdLibPlcEntity of
        AnonStdLibType ty   -> onType plcName ty
        AnonStdLibTerm term -> onTerm plcName term

-- | Fold a 'StdLibFsEntity'.
foldStdLibFsEntity
    :: (String -> [a] -> a)                          -- ^ What to do on a folder or a file.
    -> (String -> Quote (Type TyName ())      -> a)  -- ^ What to do on a type.
    -> (String -> Quote (Term TyName Name ()) -> a)  -- ^ What to do on a term.
    -> StdLibFsEntity
    -> a
foldStdLibFsEntity onFs onType onTerm = go where
    go (Named fsName anonStdLibFsEntity) = onFs fsName $ case anonStdLibFsEntity of
        AnonStdLibFolder fsEntities  -> map go fsEntities
        AnonStdLibFile   plcEntities -> map (foldStdLibPlcEntity onType onTerm) plcEntities

-- | Fold the entire stdlib.
foldStdLib
    :: (String -> [a] -> a)                          -- ^ What to do on a folder or a file.
    -> (String -> Quote (Type TyName ())      -> a)  -- ^ What to do on a type.
    -> (String -> Quote (Term TyName Name ()) -> a)  -- ^ What to do on a term.
    -> a
foldStdLib onFs onType onTerm = foldStdLibFsEntity onFs onType onTerm stdLib

-- | The entire stdlib exported as a single value.
stdLib :: StdLibFsEntity
stdLib
    = Named "StdLib" $ AnonStdLibFolder
        [ Named "Data" $ AnonStdLibFolder
            [ Named "Bool" $ AnonStdLibFile
                [ Named "Bool"  $ AnonStdLibType getBuiltinBool
                , Named "True"  $ AnonStdLibTerm getBuiltinTrue
                , Named "False" $ AnonStdLibTerm getBuiltinFalse
                , Named "If"    $ AnonStdLibTerm getBuiltinIf
                ]
            , Named "ChurchNat" $ AnonStdLibFile
                [ Named "ChurchNat"  $ AnonStdLibType getBuiltinChurchNat
                , Named "ChurchZero" $ AnonStdLibTerm getBuiltinChurchZero
                , Named "ChurchSucc" $ AnonStdLibTerm getBuiltinChurchSucc
                ]
            , Named "Function" $ AnonStdLibFile
                [ Named "Const"  $ AnonStdLibTerm getBuiltinConst
                -- , Named "Self"   $ AnonStdLibType getBuiltinSelf
                , Named "Unroll" $ AnonStdLibTerm getBuiltinUnroll
                , Named "Fix"    $ AnonStdLibTerm getBuiltinFix
                , Named "Fix2"   $ AnonStdLibTerm (getBuiltinFixN 2)
                ]
            , Named "List" $ AnonStdLibFile
                [ -- Named "List"      $ AnonStdLibType getBuiltinList
                  Named "Nil"       $ AnonStdLibTerm getBuiltinNil
                , Named "Cons"      $ AnonStdLibTerm getBuiltinCons
                , Named "FoldrList" $ AnonStdLibTerm getBuiltinFoldrList
                , Named "FoldList"  $ AnonStdLibTerm getBuiltinFoldList
                ]
            , Named "Nat" $ AnonStdLibFile
                [ -- Named "Nat"      $ AnonStdLibType getBuiltinNat
                  Named "Zero"     $ AnonStdLibTerm getBuiltinZero
                , Named "Succ"     $ AnonStdLibTerm getBuiltinSucc
                , Named "FoldrNat" $ AnonStdLibTerm getBuiltinFoldrNat
                , Named "FoldNat"  $ AnonStdLibTerm getBuiltinFoldNat
                ]
            , Named "Unit" $ AnonStdLibFile
                [ Named "Unit"    $ AnonStdLibType getBuiltinUnit
                , Named "Unitval" $ AnonStdLibTerm getBuiltinUnitval
                ]
            ]
        ]
-- Commented out types are of the 'HoledType' form which will vanish in future.
