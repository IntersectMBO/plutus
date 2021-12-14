-- |
-- Module      : Foundation.VFS.FilePath
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--
-- # Opaque implementation for FilePath
--
-- The underlying type of a FilePath is a `Foundation.ByteArray`. It is indeed like
-- this because for some systems (Unix systems) a `FilePath` is a null
-- terminated array of bytes.
--
-- # FilePath and FileName for type checking validation
--
-- In order to add some constraint at compile time, it is not possible to
-- append (`</>`) a `FilePath` to another `FilePath`.
-- You can only append (`</>`) a `FileName` to a given `FilePath`.
--

{-# LANGUAGE CPP #-}

module Foundation.VFS.FilePath
    ( FilePath
    , Relativity(..)
    , FileName
      -- * conversion
    , filePathToString
    , filePathToLString

      -- ** unsafe
    , unsafeFilePath
    , unsafeFileName
    , extension
    ) where

import Basement.Compat.Base
import Basement.Compat.Semigroup
import Foundation.Collection
import Foundation.Array
import Foundation.String (Encoding(..), ValidationFailure, toBytes, fromBytes, String)
import Foundation.VFS.Path(Path(..))

import qualified Data.List
-- ------------------------------------------------------------------------- --
--                           System related helpers                          --
-- ------------------------------------------------------------------------- --

#ifdef mingw32_HOST_OS
pathSeparatorWINC :: Char
pathSeparatorWINC = '\\'

-- | define the Path separator for Windows systems : '\\'
pathSeparatorWIN :: String
pathSeparatorWIN = fromString [pathSeparatorWINC]
#else
pathSeparatorPOSIXC :: Char
pathSeparatorPOSIXC = '/'

-- | define the Path separator for POSIX systems : '/'
pathSeparatorPOSIX :: String
pathSeparatorPOSIX = fromString [pathSeparatorPOSIXC]
#endif

pathSeparatorC :: Char
pathSeparator :: String
#ifdef mingw32_HOST_OS
pathSeparatorC = pathSeparatorWINC
pathSeparator = pathSeparatorWIN
#else
pathSeparatorC = pathSeparatorPOSIXC
pathSeparator = pathSeparatorPOSIX
#endif

-- ------------------------------------------------------------------------- --
--                              FilePath                                     --
-- ------------------------------------------------------------------------- --

-- | information about type of FilePath
--
-- A file path being only `Relative` or `Absolute`.
data Relativity = Absolute | Relative
  deriving (Eq, Show)

-- | FilePath is a collection of FileName
--
-- TODO: Eq and Ord are implemented using Show
--       This is not very efficient and would need to be improved
--       Also, it is possible the ordering is not necessary what we want
--       in this case.
--
-- A FilePath is one of the following:
--
-- * An Absolute:
--   * starts with one of the follwing "/"
-- * A relative:
--   * don't start with a "/"
--
-- * authorised:
--   * "/"
--   * "/file/path"
--   * "."
--   * ".."
--   * "work/haskell/hs-foundation"
--
-- * unauthorised
--   * "path//"
data FilePath = FilePath Relativity [FileName]

instance Show FilePath where
    show = filePathToLString
instance Eq FilePath where
  (==) a b = (==) (show a) (show b)
instance Ord FilePath where
  compare a b = compare (show a) (show b)

-- | error associated to filepath manipulation
data FilePath_Invalid
      = ContiguousPathSeparator
          -- ^ this mean there were 2 contiguous path separators.
          --
          -- This is not valid in Foundation's FilePath specifications
    deriving (Typeable, Show)
instance Exception FilePath_Invalid

instance IsString FilePath where
    fromString [] = FilePath Absolute mempty
    fromString s@(x:xs)
        | hasContigueSeparators s = throw ContiguousPathSeparator
        | otherwise = FilePath relativity $ case relativity of
            Absolute -> fromString <$> splitOn isSeparator xs
            Relative -> fromString <$> splitOn isSeparator s
      where
        relativity :: Relativity
        relativity = if isSeparator x then Absolute else Relative

-- | A filename (or path entity) in the FilePath
--
-- * Authorised
--   * ""
--   * "."
--   * ".."
--   * "foundation"
-- * Unauthorised
--   * "/"
--   * "file/"
--   * "/file"
--   * "file/path"
--
data FileName = FileName (UArray Word8)
  deriving (Eq)
-- | errors related to FileName manipulation
data FileName_Invalid
    = ContainsNullByte
        -- ^ this means a null byte was found in the FileName
    | ContainsSeparator
        -- ^ this means a path separator was found in the FileName
    | EncodingError ValidationFailure
        -- ^ encoding error
    | UnknownTrailingBytes (UArray Word8)
        -- ^ some unknown trainling bytes found
  deriving (Typeable, Show)
instance Exception FileName_Invalid

instance Show FileName where
    show = fileNameToLString
instance IsString FileName where
  fromString [] = FileName mempty
  fromString xs | hasNullByte  xs = throw ContainsNullByte
                | hasSeparator xs = throw ContainsSeparator
                | otherwise       = FileName $ toBytes UTF8 $ fromString xs

hasNullByte :: [Char] -> Bool
hasNullByte = Data.List.elem '\0'

hasSeparator :: [Char] -> Bool
hasSeparator = Data.List.elem pathSeparatorC

isSeparator :: Char -> Bool
isSeparator = (==) pathSeparatorC

hasContigueSeparators :: [Char] -> Bool
hasContigueSeparators [] = False
hasContigueSeparators [_] = False
hasContigueSeparators (x1:x2:xs) =
    (isSeparator x1 && x1 == x2) || hasContigueSeparators xs

instance Semigroup FileName where
    (<>) (FileName a) (FileName b) = FileName $ a `mappend` b
instance Monoid FileName where
    mempty = FileName mempty
    mappend (FileName a) (FileName b) = FileName $ a `mappend` b

instance Path FilePath where
    type PathEnt FilePath = FileName
    type PathPrefix FilePath = Relativity
    type PathSuffix FilePath = ()
    (</>) = join
    splitPath (FilePath r xs) = (r, xs, ())
    buildPath (r, xs , _) = FilePath r xs

-- compare to the original </>, this type disallow to be able to append an absolute filepath to a filepath
join :: FilePath -> FileName -> FilePath
join p              (FileName x) | null x = p
join (FilePath r xs) x          = FilePath r $ snoc xs x

filePathToString :: FilePath -> String
filePathToString (FilePath Absolute []) = fromString [pathSeparatorC]
filePathToString (FilePath Relative []) = fromString "."
filePathToString (FilePath Absolute fns) = cons pathSeparatorC $ filenameIntercalate fns
filePathToString (FilePath Relative fns) = filenameIntercalate fns

filenameIntercalate :: [FileName] -> String
filenameIntercalate = mconcat . Data.List.intersperse pathSeparator . fmap fileNameToString

-- | convert a FileName into a String
--
-- This function may throw an exception associated to the encoding
fileNameToString :: FileName -> String
fileNameToString (FileName fp) =
    -- FIXME probably incorrect considering windows.
    -- this is just to get going to be able to be able to reuse System.IO functions which
    -- works on [Char]
    case fromBytes UTF8 fp of
        (s, Nothing, bs)
            | null bs -> s
            | otherwise -> throw $ UnknownTrailingBytes bs
        (_, Just err, _) -> throw $ EncodingError err

-- | conversion of FileName into a list of Char
--
-- this function may throw exceptions
fileNameToLString :: FileName -> [Char]
fileNameToLString = toList . fileNameToString

-- | conversion of a FilePath into a list of Char
--
-- this function may throw exceptions
filePathToLString :: FilePath -> [Char]
filePathToLString = toList . filePathToString

-- | build a file path from a given list of filename
--
-- this is unsafe and is mainly needed for testing purpose
unsafeFilePath :: Relativity -> [FileName] -> FilePath
unsafeFilePath = FilePath

-- | build a file name from a given ByteArray
--
-- this is unsafe and is mainly needed for testing purpose
unsafeFileName :: UArray Word8 -> FileName
unsafeFileName = FileName

extension :: FileName -> Maybe FileName
extension (FileName fn) = case splitOn (\c -> c == 0x2E) fn of
                            []  -> Nothing
                            [_] -> Nothing
                            xs  -> Just $ FileName $ last $ nonEmpty_ xs
