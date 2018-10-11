{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.TypeSynthesis.Error ( dummyTyName
                                               , dummyKind
                                               , dummyType
                                               ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyNameWithKind ()
dummyTyName = TyNameWithKind (TyName (Name ((), Type ()) "*" dummyUnique))

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyNameWithKind ()
dummyType = TyVar () dummyTyName
