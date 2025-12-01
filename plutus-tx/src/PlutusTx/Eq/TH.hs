{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Eq.TH (Eq (..), deriveEq) where

import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Data.Traversable
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as TH
import PlutusTx.Bool (Bool (True), (&&))
import PlutusTx.Eq.Class
import Prelude hiding (Bool (True), Eq, (&&), (==))

{-| derive a PlutusTx.Eq instance for a datatype/newtype, similar to Haskell's `deriving stock Eq`.

One shortcoming compared to Haskell's deriving is that you cannot `PlutusTx.deriveEq` for polymorphic phantom types. -}
deriveEq :: TH.Name -> TH.Q [TH.Dec]
deriveEq name = do
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
    instanceCxt = TH.AppT (TH.ConT ''Eq) <$> tyVars
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Eq) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

  pure
    <$> instanceD
      (pure instanceCxt)
      (pure instanceType)
      [ funD '(==) (fmap deriveEqCons cons <> [pure eqDefaultClause])
      , TH.pragInlD '(==) TH.Inlinable TH.FunLike TH.AllPhases
      ]

-- Clause:    Cons1 l1 l2 l3 .. ln == Cons1 r1 r2 r3 .. rn
deriveEqCons :: ConstructorInfo -> Q Clause
deriveEqCons (ConstructorInfo {constructorName = name, constructorFields = fields}) =
  do
    argsL <- for [1 .. length fields] $ \i -> TH.newName ("l" <> show i <> "l")
    argsR <- for [1 .. length fields] $ \i -> TH.newName ("r" <> show i <> "r")
    pure
      ( TH.Clause
          [ConP name [] (fmap VarP argsL), ConP name [] (fmap VarP argsR)]
          ( NormalB $
              case fields of
                [] -> TH.ConE 'True
                _ ->
                  foldr1 (\e acc -> TH.InfixE (pure e) (TH.VarE '(&&)) (pure acc)) $
                    zipWith
                      ( \argL argR ->
                          TH.InfixE (pure $ TH.VarE argL) (TH.VarE '(==)) (pure $ TH.VarE argR)
                      )
                      argsL
                      argsR
          )
          []
      )

-- Clause:  _ == _ = False
eqDefaultClause :: Clause
eqDefaultClause = TH.Clause [WildP, WildP] (TH.NormalB (ConE 'False)) []
