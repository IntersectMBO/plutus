{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Enum.TH (Enum (..), deriveEnum) where

import Control.Monad
import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Data.Tuple
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as TH
import PlutusTx.Enum.Class
import PlutusTx.ErrorCodes
import PlutusTx.Trace
import Prelude hiding (Bool (True), Enum (..), Eq, (&&), (==))

data SuccPred = Succ | Pred

{-| Derive PlutusTx.Enum typeclass for datatypes, much like `deriving stock Enum` does for Haskell

Note: requires enabling OverloadedStrings language extension -}
deriveEnum :: TH.Name -> TH.Q [TH.Dec]
deriveEnum name = do
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
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Enum) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

    table = zip (fmap IntegerL [0 ..]) (fmap constructorName cons)

  when (null cons) $
    fail $
      "Can't make a derived instance of `Enum "
        ++ show tyConName
        ++ "`: "
        ++ show tyConName
        ++ " must must be an enumeration type (an enumeration consists of one or more nullary, non-GADT constructors)"

  pure
    <$> instanceD
      (pure [])
      (pure instanceType)
      [ funD 'succ (fmap (deriveSuccPred Succ) (zip cons (tail (Just <$> cons) ++ [Nothing])))
      , TH.pragInlD 'succ TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'pred (fmap (deriveSuccPred Pred) (zip cons (Nothing : init (Just <$> cons))))
      , TH.pragInlD 'pred TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'toEnum $ fmap deriveToEnum table <> [pure toEnumDefaultClause]
      , TH.pragInlD 'toEnum TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'fromEnum $ fmap (deriveFromEnum . swap) table
      , TH.pragInlD 'fromEnum TH.Inlinable TH.FunLike TH.AllPhases
      ]

toEnumDefaultClause :: Clause
toEnumDefaultClause =
  TH.Clause
    [WildP]
    ( TH.NormalB $
        AppE (VarE 'traceError) (VarE 'toEnumBadArgumentError)
    )
    []

deriveToEnum :: (Lit, Name) -> Q Clause
deriveToEnum (l, n) = pure (TH.Clause [LitP l] (NormalB $ ConE n) [])

deriveFromEnum :: (Name, Lit) -> Q Clause
deriveFromEnum (n, l) = pure (TH.Clause [ConP n [] []] (NormalB $ LitE l) [])

deriveSuccPred :: SuccPred -> (ConstructorInfo, Maybe ConstructorInfo) -> Q Clause
deriveSuccPred
  succPred
  ( ConstructorInfo {constructorName = nameL, constructorFields = []}
    , Nothing
    ) =
    pure
      ( TH.Clause
          [ConP nameL [] []]
          ( NormalB $
              AppE
                (VarE 'traceError)
                ( VarE $ case succPred of
                    Succ -> 'succBadArgumentError
                    Pred -> 'predBadArgumentError
                )
          )
          []
      )
deriveSuccPred
  _
  ( ConstructorInfo {constructorName = nameL, constructorFields = []}
    , Just ConstructorInfo {constructorName = nameR, constructorFields = []}
    ) =
    pure
      ( TH.Clause
          [ConP nameL [] []]
          (NormalB $ ConE nameR)
          []
      )
deriveSuccPred _ _ = fail "Can't make a derived instance of Enum when constructor has fields"
