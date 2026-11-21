-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-| This module assigns types to built-ins.
See the @plutus/plutus-core/docs/Constant application.md@
article for how this emerged. -}
module PlutusCore.Builtin.TypeScheme
  ( Typeable
  , TypeScheme (..)
  , argProxy
  , typeSchemeToType
  ) where

import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Core
import PlutusCore.Name.Unique

import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.Text qualified as Text
import Data.Typeable
import GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- We have these 'Typeable' constraints here just for the generators tests. It's fine since
-- 'TypeScheme' is not used for evaluation and so we can shove into 'TypeScheme' whatever we want.
{-| The type of type schemes of built-in functions.
@args@ is a list of types of arguments, @res@ is the resulting type.
E.g. @Text -> Bool -> Integer@ is encoded as @TypeScheme val [Text, Bool] Integer@. -}
data TypeScheme val (args :: [GHC.Type]) res where
  TypeSchemeResult
    :: (Typeable res, KnownTypeAst TyName (UniOf val) res, MakeKnown val res)
    => TypeScheme val '[] res
  -- Arguments need only unlifting, so argument-only views need no way to rebuild a value.
  TypeSchemeArrow
    :: (Typeable arg, KnownTypeAst TyName (UniOf val) arg, ReadKnown val arg)
    => TypeScheme val args res -> TypeScheme val (arg ': args) res
  TypeSchemeAll
    :: (KnownSymbol text, KnownNat uniq, KnownKind kind)
    => Proxy '(text, uniq, kind)
    -> TypeScheme val args res
    -> TypeScheme val args res

argProxy :: TypeScheme val (arg ': args) res -> Proxy arg
argProxy _ = Proxy

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
typeSchemeToType :: TypeScheme val args res -> Type TyName (UniOf val) ()
typeSchemeToType sch@TypeSchemeResult = toTypeAst sch
typeSchemeToType sch@(TypeSchemeArrow schB) =
  TyFun () (toTypeAst $ argProxy sch) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll (_ :: Proxy '(text, uniq, kind)) schB) =
  let text = Text.pack $ symbolVal @text Proxy
      uniq = fromIntegral $ natVal @uniq Proxy
      a = TyName $ Name text $ Unique uniq
   in TyForall () a (demoteKind $ knownKind @kind) $ typeSchemeToType schB

-- The precedence of @->@ is @-1@, which is why this number appears in the implementation of the
-- instance.
instance Show (TypeScheme val args res) where
  showsPrec p sch@TypeSchemeResult =
    showParen (p > 0) $
      showsPrec (-1) (typeRep sch)
  showsPrec p sch@(TypeSchemeArrow schB) =
    showParen (p > 0) $ -- @0@ is to account for associativity, see https://stackoverflow.com/a/43639618
      showsPrec 0 (typeRep $ argProxy sch)
        . showString " -> "
        . showsPrec (-1) schB
  showsPrec p (TypeSchemeAll (_ :: Proxy '(text, uniq, kind)) schB) =
    showParen (p > 0) $
      showString "forall "
        . showString (symbolVal @text Proxy)
        . showString ". "
        . showsPrec 0 schB
