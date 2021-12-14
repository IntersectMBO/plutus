-- |
-- Module      : Foundation.VFS.Path
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--

{-# LANGUAGE FlexibleContexts #-}

module Foundation.VFS.Path
    (
      -- * Path class
      Path(..)

    , parent
    , filename
    , prefix
    , suffix
    ) where

import Basement.Compat.Base

-- $setup
-- >>> import Basement.Compat.Base
-- >>> import Foundation.VFS.FilePath
-- >>> import Foundation.VFS.Path

-- | Path type class
--
-- defines the Path associated types and basic functions to implement related
-- to the path manipulation
--
-- # TODO, add missing enhancement:
--
-- @
-- splitExtension :: PathEnt path -> (PathEnt path, PathEnt path)
-- addExtension  :: PathEnt path -> PathEnt path -> PathEnt path
-- (<.>) :: path -> PathEnt path -> path
-- (-<.>) :: path -> PathEnt path -> path
-- @
--
class Path path where
    -- | the associated PathEntity of the given `path`
    -- this type is the minimal element contained in the Path
    -- a Path is not a collection but it is possible to see this
    -- associated type equivalent to the `Foundation.Collection.Element` type family
    type PathEnt path

    -- | the associated prefix of the given `path`
    --
    -- in the case of a `Foundation.VFS.FilePath`, it is a void (i.e. `()`)
    -- in the case of a `Foundation.VFS.URI`, it is the schema, host, port...
    type PathPrefix path

    -- | the associated suffix of the given path
    --
    -- in the case of the `Foundation.VFS.FilePath`, it is a void (i.e. `()`)
    -- in the case of the `Foundation.VFS.URI`, it is a the query, the fragment
    type PathSuffix path

    -- | join a path entity to a given path
    (</>) :: path -> PathEnt path -> path

    -- | split the path into the associated elements
    splitPath :: path -> ( PathPrefix path
                         , [PathEnt path]
                         , PathSuffix path
                         )

    -- | build the path from the associated elements
    buildPath :: ( PathPrefix path
                 , [PathEnt path]
                 , PathSuffix path
                 )
              -> path


-- | parent is only going to drop the filename.
--
-- if you actually want to reference to the parent directory, simply uses:
--
-- @
-- parent "." /= "." </> ".."
-- @
--
-- >>> parent ("foo.hs" :: FilePath)
-- .
--
-- >>> parent ("foo/bar/baz.hs" :: FilePath)
-- foo/bar
parent :: Path path => path -> path
parent path = buildPath (p, init ps, s)
  where
    (p, ps, s) = splitPath path


-- | get the filename of the given path
--
-- If there is no filename, you will receive the 'mempty' of the 'PathEnt'
--
-- >>> filename ("foo.hs" :: FilePath)
-- foo.hs
--
-- >>> filename ("foo/bar/baz.hs" :: FilePath)
-- baz.hs
filename :: (Path path, Monoid (PathEnt path)) => path -> PathEnt path
filename path = case ps of
    [] -> mempty
    _  -> last ps
  where
    (_, ps , _) = splitPath path

-- TODO: this might be better in Sequential ?
init :: [a] -> [a]
init [] = []
init [_] = []
init (x:xs) = x : init xs

-- TODO: this might be better in Sequential ?
last :: [a] -> a
last [] = undefined
last [x] = x
last (_:xs) = last xs


-- | get the path prefix information
--
-- >>> prefix ("/home/tab" :: FilePath)
-- Absolute
--
-- >>> prefix ("home/tab" :: FilePath)
-- Relative
--
-- or for URI (TODO, not yet accurate)
--
-- @
-- prefix "http://github.com/vincenthz/hs-foundation?w=1"
--    == URISchema http Nothing Nothing "github.com" Nothing
-- @
prefix :: Path path => path -> PathPrefix path
prefix p = pre
  where
    (pre, _, _) = splitPath p

-- | get the path suffix information
--
-- >>> suffix ("/home/tab" :: FilePath)
-- ()
--
-- or for URI (TODO, not yet accurate)
--
-- @
-- suffix "http://github.com/vincenthz/hs-foundation?w=1"
--    == URISuffix (["w", "1"], Nothing)
-- @
suffix :: Path path => path -> PathSuffix path
suffix p = suf
  where
    (_, _, suf) = splitPath p
