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

termIsSerializable :: BuiltinsInfo uni fun -> Term name uni fun a -> Bool
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

{- Note [Unserializable constants]
Generally we require that programs are (de-)serializable, which requires that all constants
in the program are (de-)serializable. This is enforced by the type system, we have to
have instances for all builtin types in the universe.

However, in practice we have to limit this somewhat. In particular, some builtin types
have no _cheap_ (de-)serialization method. This notably applies to the BLS constants, where
both BLS "deserialization" and "uncompression" do some sanity checks that take a non-trivial
amount of time.

This is a problem: in our time budgeting for validating transactions we generally assume
that deserialization is proportional to input size with low constant factors. But for a
malicious program made up of only BLS points, this would not be true!

So pragmatically we disallow (de-)serialization of constants of such types (the instances
still exist, but they will fail at runtime). The problem then is that we need to make
sure that we don't accidentally create any such constants. It's one thing if the _user_
does it - then we can just tell them not to (there are usually workarounds). But the
compiler should also not do it! Notably, the EvaluateBuiltins pass can produce _new_
constants.

To deal with this problem we pass around a predicate that tells us which constants are
bad, so we can just refuse to perform a transformation if it would produce unrepresentable
constants.

An alternative approach would be to instead add a pass to rewrite the problematic
constants into a non-problematic form (e.g. conversion from a bytestring instead of a constant).
This would be better for optimization, since we wouldn't be blocking EvaluateBuiltins
from working, even if it was good, but it has two problems:
1. It would fight with EvaluateBuiltins, which each undoing the other.
2. It can't work generically, since we don't always have a way to do the transformation. In
particular, there isn't a way to do this for the ML-result BLS type.
-}
