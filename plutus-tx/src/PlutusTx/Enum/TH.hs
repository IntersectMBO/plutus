{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module PlutusTx.Enum.TH (Enum (..), deriveEnum, deriveEnumData) where

import Control.Monad
import Data.Deriving.Internal (varTToName)
import Data.Foldable
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as TH
import PlutusTx.Enum.Class
import PlutusTx.ErrorCodes
import PlutusTx.Trace
import PlutusTx.IsData.Class
import PlutusTx.Builtins (mkI, unsafeDataAsI, equalsInteger, error, matchData')
import Prelude hiding (Bool (True), Enum (..), Eq, (&&), (==), error)

data SuccPred = Succ | Pred
  deriving stock (Show)

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

    table = zip (fmap constructorName cons) (fmap IntegerL [0 ..])

  when (null cons) $
    fail $
      "Can't make a derived instance of `Enum "
        ++ show tyConName
        ++ "`: "
        ++ show tyConName
        ++ " must must be an enumeration type (an enumeration consists of one or more nullary, non-GADT constructors)"

  sequence [ instanceEnum tyConName tyVars cons table
           ]


{-| Derive PlutusTx.Enum typeclass for datatypes, much like `deriving stock Enum` does for Haskell

It also derives ToData/FromData/UnsafeFromData but without using Constr tag and using the more efficient I tag.

Note: requires enabling OverloadedStrings language extension -}
deriveEnumData :: TH.Name -> TH.Q [TH.Dec]
deriveEnumData name = do
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

    table = zip (fmap constructorName cons) (fmap IntegerL [0 ..])

  when (null cons) $
    fail $
      "Can't make a derived instance of `Enum "
        ++ show tyConName
        ++ "`: "
        ++ show tyConName
        ++ " must must be an enumeration type (an enumeration consists of one or more nullary, non-GADT constructors)"

  sequence [ instanceEnum tyConName tyVars cons table
           , instanceToData tyConName tyVars table
           , instanceFromData tyConName tyVars table
           , instanceUnsafeFromData tyConName tyVars table
           ]


instanceEnum :: Name -> [TH.Type] -> [ConstructorInfo] -> [(Name, Lit)] -> TH.Q TH.Dec
instanceEnum tyConName tyVars cons table =
  instanceD
      (pure [])
      (pure instanceType)
      [ funD 'succ (fmap (succPredClause Succ) (zip cons (tail (Just <$> cons) ++ [Nothing])))
      , TH.pragInlD 'succ TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'pred (fmap (succPredClause Pred) (zip cons (Nothing : init (Just <$> cons))))
      , TH.pragInlD 'pred TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'toEnum $ fmap toEnumClause table <> [pure toEnumDefaultClause]
      , TH.pragInlD 'toEnum TH.Inlinable TH.FunLike TH.AllPhases
      , funD 'fromEnum $ fmap fromEnumClause table
      , TH.pragInlD 'fromEnum TH.Inlinable TH.FunLike TH.AllPhases
      ]
  where
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Enum) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

toEnumDefaultClause :: Clause
toEnumDefaultClause =
  TH.Clause
    [WildP]
    ( TH.NormalB $
        AppE (VarE 'traceError) (VarE 'toEnumBadArgumentError)
    )
    []

toEnumClause :: (Name, Lit) -> Q Clause
toEnumClause (n, l) = do
  lhs <- newName "lhs"
  -- a guard to overcome plinth's limitation of compiling integer pattern matches
  pure (TH.Clause [VarP lhs] (GuardedB [(NormalG (AppE (AppE (VarE 'equalsInteger) (VarE lhs)) (LitE l)), ConE n)]) [])

fromEnumClause :: (Name, Lit) -> Q Clause
fromEnumClause (n, l) = pure (TH.Clause [ConP n [] []] (NormalB $ LitE l) [])

succPredClause :: SuccPred -> (ConstructorInfo, Maybe ConstructorInfo) -> Q Clause
succPredClause
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
succPredClause
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
succPredClause _ _ = fail "Can't make a derived instance of Enum when constructor has fields"


instanceToData :: Name -> [TH.Type] -> [(Name, Lit)] -> TH.Q TH.Dec
instanceToData tyConName tyVars table =
  instanceD
      (pure [])
      (pure instanceType)
      [ funD 'toBuiltinData $ fmap toDataClause table
      , TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
      ]
  where
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''ToData) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

toDataClause :: (Name, Lit) -> Q Clause
toDataClause (n, l) = pure (TH.Clause [ConP n [] []] (NormalB $ AppE (VarE 'mkI) (LitE l)) [])

instanceFromData :: Name -> [TH.Type] -> [(Name, Lit)] -> TH.Q TH.Dec
instanceFromData tyConName tyVars table =
  instanceD
      (pure [])
      (pure instanceType)
      [ funD 'fromBuiltinData [fromDataClause table]
      , TH.pragInlD 'fromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
      ]
  where
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''FromData) $ foldl' TH.AppT (TH.ConT tyConName) tyVars


fromDataClause :: [(Name, Lit)] -> Q Clause
fromDataClause table = do
  input <- newName "input"
  decoded <- newName "decoded"
  let foldedIf = foldr (\(n,l) acc -> CondE
                                      -- if
                                      (toPredicate l)
                                      -- then
                                      (AppE (ConE 'Just) (ConE n))
                                      -- else
                                      acc)
                                      (ConE 'Nothing) table
      toPredicate l = AppE (AppE (VarE 'equalsInteger) (VarE decoded)) (LitE l)

      integerLam = lamE [varP decoded] $ pure foldedIf

  TH.clause [varP input] (normalB
                          [| matchData' $(varE input)
                            (\_ _ -> Nothing)
                            (\_ -> Nothing)
                            (\_ -> Nothing)
                            $(integerLam)
                            (\_ -> Nothing) |]
                         ) []


instanceUnsafeFromData :: Name -> [TH.Type] -> [(Name, Lit)] -> TH.Q TH.Dec
instanceUnsafeFromData tyConName tyVars table =
  instanceD
      (pure [])
      (pure instanceType)
      [ funD 'unsafeFromBuiltinData [unsafeFromDataClause table]
      , TH.pragInlD 'unsafeFromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
      ]
  where
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''UnsafeFromData) $ foldl' TH.AppT (TH.ConT tyConName) tyVars

unsafeFromDataClause :: [(Name, Lit)] -> Q Clause
unsafeFromDataClause table = do
  input <- newName "input"
  decoded <- newName "decoded"
  let foldedIf = foldr (\(n,l) acc -> CondE
                                      -- if
                                      (toPredicate l)
                                      -- then
                                      (ConE n)
                                      -- else
                                      acc)
                                      (AppE (VarE 'error) (ConE '())) table
      toPredicate l = AppE (AppE (VarE 'equalsInteger) (VarE decoded)) (LitE l)

  -- let decoded = unsafeDataAsI input in if (decoded == 0) then Cons0 else ... if (decoded == n) then ConsN else error
  pure $ TH.Clause [VarP input] (NormalB
                                       (LetE [ValD (VarP decoded) (NormalB (AppE (VarE 'unsafeDataAsI) (VarE input))) [] ] foldedIf)
                                      ) []
