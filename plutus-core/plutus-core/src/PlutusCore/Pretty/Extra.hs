{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Pretty-printing stuff, some of which should probably go into the main library.
module PlutusCore.Pretty.Extra
  ( PrettyParens
  , juxtRenderContext
  ) where

import PlutusPrelude

import Control.Monad.Trans.Reader
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Profunctor
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector.Strict (Vector)
import Text.PrettyBy.Fixity
import Text.PrettyBy.Internal

type instance HasPrettyDefaults (Sole config) = HasPrettyDefaults config

instance Profunctor InContextM where
  lmap
    :: forall config' config a
     . (config' -> config)
    -> InContextM config a
    -> InContextM config' a
  lmap = coerce (withReader :: (config' -> config) -> Reader config a -> Reader config' a)
  {-# INLINE lmap #-}

  rmap
    :: forall config a b
     . (a -> b)
    -> InContextM config a
    -> InContextM config b
  rmap = coerce (mapReader :: (a -> b) -> Reader config a -> Reader config b)
  {-# INLINE rmap #-}

-- | For pretty-printing a value with a minimum amount of parens.
type PrettyParens = PrettyBy RenderContext

{-| An initial 'RenderContext'.
An expression printed in this context gets enclosed in parens unless its outermost operator (if
any) binds even stronger than function application. -}
juxtRenderContext :: RenderContext
juxtRenderContext = RenderContext ToTheRight juxtFixity

instance PrettyDefaultBy config [(k, v)] => DefaultPrettyBy config (Map k v) where
  defaultPrettyBy config = prettyBy config . Map.toList
deriving via
  PrettyCommon (Map k v)
  instance
    PrettyDefaultBy config (Map k v) => PrettyBy config (Map k v)

instance PrettyDefaultBy config [a] => DefaultPrettyBy config (Set a) where
  defaultPrettyBy config = prettyBy config . Set.toList
deriving via
  PrettyCommon (Set a)
  instance
    PrettyDefaultBy config (Set a) => PrettyBy config (Set a)

instance PrettyDefaultBy config [a] => DefaultPrettyBy config (Vector a) where
  defaultPrettyBy config = prettyBy config . toList
deriving via
  PrettyCommon (Vector a)
  instance
    PrettyDefaultBy config (Vector a) => PrettyBy config (Vector a)
