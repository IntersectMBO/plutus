{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Bounded.TH (Bounded (..), deriveBounded) where

import Control.Monad
import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as TH
import PlutusTx.Bounded.Class
import Prelude hiding (Bounded (..))

data MinMax = Min | Max

-- | Derive PlutusTx.Bounded typeclass for datatypes, much like `deriving stock Bounded` does for Haskell
deriveBounded :: TH.Name -> TH.Q [TH.Dec]
deriveBounded name = do
  TH.DatatypeInfo
    { TH.datatypeName = tyConName
    , TH.datatypeInstTypes = tyVars0
    , TH.datatypeCons = cons
    } <-
    TH.reifyDatatype name
  let
    -- The purpose of the `TH.VarT . varTToName` roundtrip is to remove the kind
    -- signatures attached to the type variables in `tyVars0`. Otherwise, the
    -- `KindSignatures` extension would be needed whenever `length tyVars0 > 0`.
    tyVars = TH.VarT . varTToName <$> tyVars0
    instanceCxt :: TH.Cxt
    instanceCxt = TH.AppT (TH.ConT ''Bounded) <$> tyVars
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Bounded) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

  when (null cons) $
    fail $
      "Can't make a derived instance of `Bounded "
        ++ show tyConName
        ++ "`: "
        ++ show tyConName
        ++ "must be an enumeration type (an enumeration consists of one or more nullary, non-GADT constructors) or "
        ++ show tyConName
        ++ " must have precisely one constructor"

  pure
    <$> instanceD
      ( pure $ case cons of
          [_] -> instanceCxt -- if single constructor, add instance context
          _ -> []
      )
      (pure instanceType)
      [ funD 'minBound (pure $ deriveXBound Min cons)
      , TH.pragInlD 'minBound TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'maxBound (pure $ deriveXBound Max cons)
      , TH.pragInlD 'maxBound TH.Inlinable TH.FunLike TH.AllPhases
      ]

deriveXBound :: MinMax -> [ConstructorInfo] -> Q Clause
deriveXBound minMax [ConstructorInfo {constructorName = nameL, constructorFields = fields}] =
  pure
    ( TH.Clause
        []
        (NormalB $ foldr (const (`AppE` (VarE $ fromMinMax minMax))) (ConE nameL) fields)
        []
    )
  where
    fromMinMax :: MinMax -> Name
    fromMinMax Min = 'minBound
    fromMinMax Max = 'maxBound
deriveXBound minMax cons = do
  unless allConsNoFields $ fail "Can't make a derived instance of Bounded when constructor has fields"
  pure
    ( TH.Clause
        []
        (NormalB $ ConE $ constructorName $ fromMinMax minMax cons)
        []
    )
  where
    fromMinMax :: MinMax -> ([a] -> a)
    fromMinMax Min = head
    fromMinMax Max = last
    allConsNoFields = foldl (\acc c -> acc && null (constructorFields c)) True cons
