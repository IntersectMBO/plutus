{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Builtin.Case where

import PlutusCore.Builtin.KnownType (HeadSpine (..))
import PlutusCore.Core.Type (Type, UniOf)
import PlutusCore.Name.Unique (TyName)

import Control.DeepSeq (NFData (..), rwhnf)
import Data.Default.Class (Default (..))
import Data.Text (Text)
import Data.Vector (Vector)
import NoThunks.Class
import Text.PrettyBy (display)
import Universe

class AnnotateCaseBuiltin uni where
  {-| Given a tag for a built-in type and a list of branches, annotate each of the branches with
  its expected argument types or fail if casing on values of the built-in type isn't supported.
  Note: you don't need to include the resulting type of the whole case matching in the
  returning list here. -}
  annotateCaseBuiltin
    :: UniOf term ~ uni
    => Type TyName uni ann
    -> [term]
    -> Either Text [(term, [Type TyName uni ann])]

class CaseBuiltin uni where
  {-| Given a constant with its type tag and a vector of branches, choose the appropriate branch
  or fail if the constant doesn't correspond to any of the branches (or casing on constants of
  this type isn't supported at all). -}
  caseBuiltin
    :: UniOf term ~ uni
    => Some (ValueOf uni)
    -> Vector term
    -> HeadSpine Text term (Some (ValueOf uni))

-- See Note [DO NOT newtype-wrap functions].
{-| A @data@ version of 'CaseBuiltin'. we parameterize the evaluator by a 'CaserBuiltin' so that
the caller can choose whether to use the 'caseBuiltin' method or the always failing caser (the
latter is required for earlier protocol versions when we didn't support casing on builtins). -}
data CaserBuiltin uni = CaserBuiltin
  { unCaserBuiltin
      :: !(forall term. UniOf term ~ uni => Some (ValueOf uni) -> Vector term -> HeadSpine Text term (Some (ValueOf uni)))
  }

instance NFData (CaserBuiltin uni) where
  rnf = rwhnf

deriving via
  OnlyCheckWhnfNamed "PlutusCore.Builtin.Case.CaserBuiltin" (CaserBuiltin uni)
  instance
    NoThunks (CaserBuiltin uni)

instance CaseBuiltin uni => Default (CaserBuiltin uni) where
  def = CaserBuiltin caseBuiltin

unavailableCaserBuiltin :: Int -> CaserBuiltin uni
unavailableCaserBuiltin ver =
  CaserBuiltin $ \_ _ ->
    HeadError $
      "'case' on values of built-in types is not supported in protocol version " <> display ver
