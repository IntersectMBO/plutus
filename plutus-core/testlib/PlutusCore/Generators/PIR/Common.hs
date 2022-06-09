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


import Data.Map (Map)
import Data.Map qualified as Map
import Data.String
import Test.QuickCheck
import Text.PrettyBy

import PlutusCore.Default
import PlutusCore.Name
import PlutusIR

-- CODE REVIEW: where to put the stuff below? Can we refactor to the point where we don't need them?
-- Currently we need these for shrinking, getting rid of them would be nice.
deriving stock instance Eq (Term TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (Binding TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (VarDecl TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (TyVarDecl TyName ())
deriving stock instance Eq (Datatype TyName Name DefaultUni DefaultFun ())

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

unit :: Type tyname DefaultUni ()
unit = TyBuiltin () (SomeTypeIn DefaultUniUnit)

integer :: Type tyname DefaultUni ()
integer = TyBuiltin () (SomeTypeIn DefaultUniInteger)

bool :: Type tyname DefaultUni ()
bool = TyBuiltin () (SomeTypeIn DefaultUniBool)

-- TODO: this should probably go elsewhere
instance PrettyBy config i => PrettyBy config (NonNegative i) where
  prettyBy ctx (NonNegative i) = prettyBy ctx i

-- TODO: this should probably go elsewhere
instance ( HasPrettyDefaults config ~ 'True
         , PrettyBy config k
         , PrettyBy config v) => PrettyBy config (Map k v) where
  prettyBy ctx = prettyBy ctx . Map.toList
