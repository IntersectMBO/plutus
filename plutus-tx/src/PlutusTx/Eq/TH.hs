{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Eq.TH (Eq (..), deriveEq) where

import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Data.Traversable
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import PlutusTx.Bool (Bool (True), (&&))
import PlutusTx.Eq.Class hiding ((/=))
import Prelude hiding (Bool (True), Eq, (&&), (==))

{-| Derive a Plinth 'Eq' instance for a datatype or newtype.

Similar to Haskell's @deriving stock Eq@, this generates structural equality
with short-circuit evaluation and INLINEABLE pragmas for optimal on-chain performance.

__Usage:__

@
data MyType = Con1 Integer | Con2 Bool
deriveEq ''MyType
@

__Generated code:__

* Pattern-matching clauses for each constructor
* Short-circuit evaluation (stops at first inequality)
* @INLINEABLE@ pragma for cross-module optimization
* Proper handling of phantom type parameters

__Supported types:__

* Regular datatypes with any number of constructors
* Newtypes
* Types with phantom type parameters
* Types with strict or lazy fields
* Records
* Self-recursive types
* Mutually recursive types (when all types in the group have Eq instances)

__Unsupported:__

* GADTs (may produce type errors)
* Existentially quantified types
* Type families (not tested)

See 'PlutusTx.Eq.Class.Eq' for the class definition. -}
deriveEq :: Name -> Q [Dec]
deriveEq name = do
  DatatypeInfo
    { datatypeName = tyConName
    , datatypeInstTypes = tyVars0
    , datatypeCons = cons
    } <-
    reifyDatatype name

  roles <- reifyRoles name

  let
    -- The purpose of the `VarT . varTToName` roundtrip is to remove the kind
    -- signatures attached to the type variables in `tyVars0`. Otherwise, the
    -- `KindSignatures` extension would be needed whenever `length tyVars0 > 0`.
    tyVars = VarT . varTToName <$> tyVars0

    nonPhantomTyVars =
      VarT . varTToName . snd <$> filter ((/= PhantomR) . fst) (zip roles tyVars0)

    instanceCxt :: Cxt
    instanceCxt = AppT (ConT ''Eq) <$> nonPhantomTyVars

    instanceType :: Type
    instanceType = AppT (ConT ''Eq) $ foldl' AppT (ConT tyConName) tyVars

    maybeDefaultClause :: [ConstructorInfo] -> [Q Clause]
    maybeDefaultClause = \case
      -- if void datatype aka 0 constructors, generate a True clause
      [] -> [clause [wildP, wildP] (normalB (conE 'True)) []]
      -- if one constructor no need to generate default clause
      [_] -> []
      -- if >1 constructors, generate a False clause
      _ -> [clause [wildP, wildP] (normalB (conE 'False)) []]

  pure
    <$> instanceD
      (pure instanceCxt)
      (pure instanceType)
      [ funD '(==) (fmap deriveEqCons cons <> maybeDefaultClause cons)
      , pragInlD '(==) Inlinable FunLike AllPhases
      ]

-- Clause:    Cons1 l1 l2 l3 .. ln == Cons1 r1 r2 r3 .. rn
deriveEqCons :: ConstructorInfo -> Q Clause
deriveEqCons (ConstructorInfo {constructorName = name, constructorFields = fields}) = do
  argsL <- for [1 .. length fields] \i -> newName ("l" <> show i <> "l")
  argsR <- for [1 .. length fields] \i -> newName ("r" <> show i <> "r")
  clause
    [conP name (fmap varP argsL), conP name (fmap varP argsR)]
    ( normalB
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
