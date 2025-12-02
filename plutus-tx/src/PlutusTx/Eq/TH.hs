{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE LambdaCase #-}

module PlutusTx.Eq.TH (Eq (..), deriveEq) where

import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Data.Traversable
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import PlutusTx.Bool (Bool (True), (&&))
import PlutusTx.Eq.Class
import Prelude hiding (Bool (True), Eq, (&&), (==))

{-| derive a PlutusTx.Eq instance for a datatype/newtype, similar to Haskell's `deriving stock Eq`.

One shortcoming compared to Haskell's deriving is that you cannot `PlutusTx.deriveEq` for polymorphic phantom types. -}
deriveEq :: Name -> Q [Dec]
deriveEq name = do
  DatatypeInfo
    { datatypeName = tyConName
    , datatypeInstTypes = tyVars0
    , datatypeCons = cons
    } <-
    reifyDatatype name
  let
    -- The purpose of the `VarT . varTToName` roundtrip is to remove the kind
    -- signatures attached to the type variables in `tyVars0`. Otherwise, the
    -- `KindSignatures` extension would be needed whenever `length tyVars0 > 0`.
    tyVars = VarT . varTToName <$> tyVars0
    instanceCxt :: Cxt
    instanceCxt = AppT (ConT ''Eq) <$> tyVars
    instanceType :: Type
    instanceType = AppT (ConT ''Eq) $ foldl' AppT (ConT tyConName) tyVars

  pure
    <$> instanceD
      (pure instanceCxt)
      (pure instanceType)
      [ funD '(==) (fmap deriveEqCons cons <> maybeDefaultClause cons)
      , pragInlD '(==) Inlinable FunLike AllPhases
      ]

-- Clause:    Cons1 l1 l2 l3 .. ln == Cons1 r1 r2 r3 .. rn
deriveEqCons :: ConstructorInfo -> Q Clause
deriveEqCons (ConstructorInfo {constructorName = name, constructorFields = fields}) =
  do
    argsL <- for [1 .. length fields] $ \i -> newName ("l" <> show i <> "l")
    argsR <- for [1 .. length fields] $ \i -> newName ("r" <> show i <> "r")
    (clause
          [conP name (fmap varP argsL), conP name (fmap varP argsR)]
          ( normalB $
              case fields of
                [] -> conE 'True
                _ ->
                  foldr1 (\e acc -> infixE (pure e) (varE '(&&)) (pure acc)) $
                    zipWith
                      ( \argL argR ->
                          infixE (pure $ varE argL) (varE '(==)) (pure $ varE argR)
                      )
                      argsL
                      argsR
          )
      []
      )


maybeDefaultClause :: [ConstructorInfo] -> [Q Clause]
maybeDefaultClause = \case
  [_] -> [] -- if one constructor no need to generate default clause
  [] -> [clause [wildP, wildP] (normalB $ conE 'True) []] -- if void datatype aka 0 constructors, generate a True clause
  _ ->  [clause [wildP, wildP] (normalB $ conE 'False) []] -- if >1 constructors, generate a False clause
