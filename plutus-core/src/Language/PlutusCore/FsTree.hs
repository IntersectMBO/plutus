-- | Machinery defined in this module allows to export mulptiple Plutus Core definitions
-- (types and terms) as a single value which enables convenient testing of various procedures
-- (pretty-printing, type checking, etc): each time a function / data type is added to that value,
-- none of the tests is required to be adapted, instead all the tests see the new definition
-- automatically.

module Language.PlutusCore.FsTree
    ( FsTree (..)
    , FolderContents (..)
    , PlcEntity (..)
    , PlcFsTree
    , PlcFolderContents
    , treeFolderContents
    , plcTypeFile
    , plcTermFile
    , foldFsTree
    , foldPlcFsTree
    , foldPlcFolderContents
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

-- We use 'String's for names, because 'FilePath's are 'String's.
-- | An 'FsTree' is either a file or a folder with a list of 'FsTree's inside.
data FsTree a
    = FsFolder String (FolderContents a)
    | FsFile String a

-- | The contents of a folder. A wrapper around @[FsTree a]@.
-- Exists because of its 'Semigroup' instance which allows to concatenate two 'FolderContents's
-- without placing them into the same folder immediately, so we can have various PLC "modules"
-- (@stdlib@, @examples@, etc), define compound modules (e.g. @stdlib <> examples@) and run various
-- tests (pretty-printing, type synthesis, etc) against simple and compound modules uniformly.
newtype FolderContents a = FolderContents
    { unFolderContents :: [FsTree a]
    } deriving (Semigroup, Monoid)

-- | A 'PlcEntity' is either a 'Type' or a 'Term'.
data PlcEntity uni fun
    = PlcType (Type TyName uni ())
    | PlcTerm (Term TyName Name uni fun ())

type PlcFsTree         uni fun = FsTree         (PlcEntity uni fun)
type PlcFolderContents uni fun = FolderContents (PlcEntity uni fun)

-- | Construct an 'FsTree' out of the name of a folder and a list of 'FsTree's.
treeFolderContents :: String -> [FsTree a] -> FsTree a
treeFolderContents name = FsFolder name . FolderContents

-- | Construct a single-file 'PlcFsTree' out of a type.
plcTypeFile :: String -> Type TyName uni () -> PlcFsTree uni fun
plcTypeFile name = FsFile name . PlcType

-- | Construct a single-file 'PlcFsTree' out of a term.
plcTermFile :: String -> Term TyName Name uni fun () -> PlcFsTree uni fun
plcTermFile name = FsFile name . PlcTerm

-- | Fold a 'FsTree'.
foldFsTree
    :: (String -> [b] -> b)  -- ^ What to do on a folder.
    -> (String -> a -> b)    -- ^ What to do on a single file in a folder.
    -> FsTree a
    -> b
foldFsTree onFolder onFile = go where
    go (FsFolder name (FolderContents trees)) = onFolder name $ map go trees
    go (FsFile name x)                        = onFile name x

-- | Fold a 'PlcFsTree'.
foldPlcFsTree
    :: (String -> [b] -> b)                          -- ^ What to do on a folder.
    -> (String -> Type TyName uni ()          -> b)  -- ^ What to do on a type.
    -> (String -> Term TyName Name uni fun () -> b)  -- ^ What to do on a term.
    -> PlcFsTree uni fun
    -> b
foldPlcFsTree onFolder onType onTerm = foldFsTree onFolder onFile where
    onFile name (PlcType getTy)   = onType name getTy
    onFile name (PlcTerm getTerm) = onTerm name getTerm

-- | Fold the contents of a PLC folder.
foldPlcFolderContents
    :: (String -> [b] -> b)                          -- ^ What to do on a folder.
    -> (String -> Type TyName uni ()          -> b)  -- ^ What to do on a type.
    -> (String -> Term TyName Name uni fun () -> b)  -- ^ What to do on a term.
    -> PlcFolderContents uni fun
    -> [b]
foldPlcFolderContents onFolder onType onTerm (FolderContents trees) =
    map (foldPlcFsTree onFolder onType onTerm) trees
