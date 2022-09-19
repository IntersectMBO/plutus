{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusCore.Generators.PIR.Common where

import Data.Bifunctor
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Stack
import Test.QuickCheck.Modifiers (NonNegative (..))
import Test.QuickCheck.Property
import Text.Pretty
import Text.PrettyBy
import Text.PrettyBy.Internal

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.TypeCheck (defKindCheckConfig)
import PlutusCore.TypeCheck.Internal (inferKindM, runTypeCheckM, withTyVar)
import PlutusIR
import PlutusIR.Error

instance Testable (Either String ()) where
    property = property . \case
        Left err -> failed { reason = err }
        Right () -> succeeded

deriving newtype instance Pretty i => Pretty (NonNegative i)
instance PrettyBy config i => DefaultPrettyBy config (NonNegative i)
deriving via PrettyCommon (NonNegative i)
    instance PrettyDefaultBy config (NonNegative i) => PrettyBy config (NonNegative i)

-- | Extract all @a_i@ from @a_0 -> a_1 -> ... -> r@.
argsKind :: Kind ann -> [Kind ann]
argsKind Type{}            = []
argsKind (KindArrow _ k l) = k : argsKind l

type TypeCtx = Map TyName (Kind ())

-- | Infer the kind of a type in a given kind context
inferKind :: TypeCtx -> Type TyName DefaultUni () -> Either String (Kind ())
inferKind ctx ty =
    first display . runTypeCheckM defKindCheckConfig $
        foldr
            (uncurry withTyVar)
            (inferKindM @(Error DefaultUni DefaultFun ()) ty)
            (Map.toList ctx)

-- | Partial unsafeInferKind, useful for context where invariants are set up to guarantee
-- that types are well-kinded.
unsafeInferKind :: HasCallStack => TypeCtx -> Type TyName DefaultUni () -> Kind ()
unsafeInferKind ctx ty =
  case inferKind ctx ty of
    Left msg -> error msg
    Right k  -> k

-- | Check well-kindedness of a type in a context
checkKind :: TypeCtx -> Type TyName DefaultUni () -> Kind () -> Either String ()
checkKind ctx ty kExp =
    if kInf == Right kExp
      then Right ()
      else Left $ concat
        [ "Inferred kind is "
        , display kInf
        , " while expected "
        , display kExp
        ]
  where
    kInf = inferKind ctx ty
