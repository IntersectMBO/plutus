{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Analysis.Builtins
  ( BuiltinsInfo (..)
  , biSemanticsVariant
  , biUnserializableConstants
  , builtinArityInfo
  , constantIsSerializable
  , termIsSerializable
  , defaultUniUnserializableConstants
  ) where

import Control.Lens hiding (parts)
import Data.Kind
import Data.Proxy
import PlutusCore.Arity
import PlutusCore.Builtin
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default
import PlutusPrelude (Default (..))
import UntypedPlutusCore.Core (Term)
import UntypedPlutusCore.Core.Plated (termSubtermsDeep, _Constant)

-- | All non-static information about builtins that the compiler might want.
data BuiltinsInfo (uni :: Type -> Type) fun = BuiltinsInfo
  { _biSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
  , -- See Note [Unserializable constants]
    _biUnserializableConstants :: Some (ValueOf uni) -> Bool
  }

makeLenses ''BuiltinsInfo

instance Default (BuiltinsInfo DefaultUni DefaultFun) where
  def =
    BuiltinsInfo
      { _biSemanticsVariant = def
      , _biUnserializableConstants = defaultUniUnserializableConstants
      }

-- | Get the arity of a builtin function from the 'PLC.BuiltinInfo'.
builtinArityInfo
  :: forall uni fun
   . ToBuiltinMeaning uni fun
  => BuiltinsInfo uni fun
  -> fun
  -> Arity
builtinArityInfo binfo = builtinArity (Proxy @uni) (binfo ^. biSemanticsVariant)

constantIsSerializable
  :: forall uni fun
   . BuiltinsInfo uni fun
  -> Some (ValueOf uni)
  -> Bool
constantIsSerializable bi v = not $ _biUnserializableConstants bi v

termIsSerializable :: BuiltinsInfo uni fun -> Term name uni fun pat a -> Bool
termIsSerializable binfo =
  allOf
    (termSubtermsDeep . _Constant)
    (constantIsSerializable binfo . snd)

-- See Note [Unserializable constants]
defaultUniUnserializableConstants :: Some (ValueOf DefaultUni) -> Bool
defaultUniUnserializableConstants = \case
  Some (ValueOf DefaultUniBLS12_381_G1_Element _) -> True
  Some (ValueOf DefaultUniBLS12_381_G2_Element _) -> True
  Some (ValueOf DefaultUniBLS12_381_MlResult _) -> True
  _ -> False

{- See Note [Unserializable constants] in PlutusIR.Analysis.Builtins.
-}
