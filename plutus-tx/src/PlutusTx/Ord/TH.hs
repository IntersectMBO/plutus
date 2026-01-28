{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Ord.TH (deriveOrd) where

import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Data.Traversable
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as TH
import PlutusTx.Ord.Class
import Prelude hiding (Bool (True), Eq ((==)), Ord (..), Ordering (..), (&&))

{- | derive a PlutusTx.Ord instance for a datatype/newtype, similar to Haskell's `deriving stock Ord`.

One shortcoming compared to Haskell's deriving is that you cannot `PlutusTx.deriveOrd` for polymorphic phantom types.
-}
deriveOrd :: TH.Name -> TH.Q [TH.Dec]
deriveOrd name = do
  TH.DatatypeInfo
    { TH.datatypeName = tyConName
    , TH.datatypeInstTypes = tyVars0
    , TH.datatypeCons = cons
    } <-
    TH.reifyDatatype name

  roles <- reifyRoles name

  let
    -- The purpose of the `TH.VarT . varTToName` roundtrip is to remove the kind
    -- signatures attached to the type variables in `tyVars0`. Otherwise, the
    -- `KindSignatures` extension would be needed whenever `length tyVars0 > 0`.
    tyVars = TH.VarT . varTToName <$> tyVars0

    nonPhantomTyVars = VarT . varTToName . snd <$> filter ((/= PhantomR) . fst) (zip roles tyVars0)

    instanceCxt :: TH.Cxt
    instanceCxt = TH.AppT (TH.ConT ''Ord) <$> nonPhantomTyVars

    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Ord) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

  pure
    <$> instanceD
      (pure instanceCxt)
      (pure instanceType)
      [ funD 'compare (fmap deriveOrdSame cons ++ maybeDeriveOrdDifferent cons)
      , TH.pragInlD 'compare TH.Inlinable TH.FunLike TH.AllPhases
      ]

deriveOrdSame :: ConstructorInfo -> Q Clause
deriveOrdSame (ConstructorInfo {constructorName = name, constructorFields = fields}) = do
  argsL <- for [1 .. length fields] $ \i -> TH.newName ("l" <> show i <> "l")
  argsR <- for [1 .. length fields] $ \i -> TH.newName ("r" <> show i <> "r")
  pure
    ( TH.Clause
        [ConP name [] (fmap VarP argsL), ConP name [] (fmap VarP argsR)]
        ( NormalB $
            case fields of
              [] -> TH.ConE 'EQ
              _ ->
                foldr1 (\e acc -> TH.InfixE (pure e) (TH.VarE '(<>)) (pure acc)) $
                  zipWith
                    ( \argL argR ->
                        TH.InfixE (pure $ TH.VarE argL) (TH.VarE 'compare) (pure $ TH.VarE argR)
                    )
                    argsL
                    argsR
        )
        []
    )

maybeDeriveOrdDifferent :: [ConstructorInfo] -> [Q Clause]
maybeDeriveOrdDifferent = \case
  [] -> [clause [wildP, wildP] (normalB $ conE 'EQ) []] -- if void datatype aka 0 constructors, generate an EQ clause
  (x : xs) -> mkLTGT [] x xs -- if >1 constructors, generate LT,GT sequences

-- OPTIMIZE: can be a small optimization here so that if lt==[] or gt==[], then use wildcard instead of generating multiple clauses
mkLTGT :: [ConstructorInfo] -> ConstructorInfo -> [ConstructorInfo] -> [Q Clause]
mkLTGT gt needle@(ConstructorInfo {constructorName = name}) lt =
  case lt of
    [] -> mkClause 'GT <$> gt -- this covers also the case of a single constructor
    (hlt : tlt) ->
      (mkClause 'LT <$> lt)
        ++ (mkClause 'GT <$> gt)
        ++ mkLTGT (needle : gt) hlt tlt
  where
    mkClause val r = clause [recP name [], recP (constructorName r) []] (normalB $ conE val) []
