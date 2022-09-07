{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}


module PlutusCore.Generators.PIR.Common where

import Data.Bifunctor
import Data.Map (Map)
import Data.Map qualified as Map
import Data.String
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

-- Some convenience definitions that make the code slightly more readable.
{-# COMPLETE Star, (:->) #-}
pattern Star :: Kind ()
pattern Star  = Type ()

pattern (:->) :: Kind () -> Kind () -> Kind ()
pattern (:->) a b = KindArrow () a b
infixr 3 :->

pattern BIF_Trace :: Term tyname name uni DefaultFun ()
pattern BIF_Trace = Builtin () Trace

pattern BIF_If :: Term tyname name uni DefaultFun ()
pattern BIF_If = Builtin () IfThenElse

pattern Const :: DefaultUni (Esc a) -> a -> Term tyname name DefaultUni fun ()
pattern Const b a = Constant () (Some (ValueOf b a))

infixr 3 ->>
(->>) :: (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ())
(->>) = TyFun ()

-- CODE REVIEW: Do these functions exist in a convenient package anywhere?
var :: String -> Int -> Name
var s i = Name (fromString s) (toEnum i)

tyvar :: String -> Int -> TyName
tyvar s i = TyName (var s i)

deriving newtype instance Pretty i => Pretty (NonNegative i)
instance PrettyBy config i => DefaultPrettyBy config (NonNegative i)
deriving via PrettyCommon (NonNegative i)
    instance PrettyDefaultBy config (NonNegative i) => PrettyBy config (NonNegative i)

-- | Extract all @a_i@ from @a_0 -> a_1 -> ... -> r@.
argsKind :: Kind ann -> [Kind ann]
argsKind Type{}            = []
argsKind (KindArrow _ k l) = k : argsKind l

-- | Infer the kind of a type in a given kind context
inferKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Either String (Kind ())
inferKind ctx ty =
    first display . runTypeCheckM defKindCheckConfig $
        foldr
            (uncurry withTyVar)
            (inferKindM @(Error DefaultUni DefaultFun ()) ty)
            (Map.toList ctx)

-- | Partial unsafeInferKind, useful for context where invariants are set up to guarantee
-- that types are well-kinded.
unsafeInferKind :: HasCallStack => Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind ()
unsafeInferKind ctx ty =
  case inferKind ctx ty of
    Left msg -> error msg
    Right k  -> k

-- | Check well-kindedness of a type in a context
checkKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind () -> Either String ()
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
