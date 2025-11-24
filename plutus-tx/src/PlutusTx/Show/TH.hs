{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module PlutusTx.Show.TH where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.List

import Data.Deriving.Internal (isInfixDataCon, isNonUnitTuple, isSym, varTToName)
import Data.List.Extra (dropEnd, foldl', intersperse)
import Data.Maybe
import Data.Traversable (for)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import Prelude (pure, (+), (<$>), (<>))
import Prelude qualified as Haskell

{-| Conversion of values to `BuiltinString`s. Unlike @GHC.Show.Show@, there is no
 @showList@ method, because there is no `Show` instance for `Data.String.String`.
-}
class Show a where
  {-# MINIMAL showsPrec | show #-}

  {-# INLINEABLE showsPrec #-}
  showsPrec :: Integer -> a -> ShowS
  showsPrec _ x ss = show x : ss

  {-# INLINEABLE show #-}
  show :: a -> BuiltinString
  show x = concatBuiltinStrings (showsPrec 0 x [])

{-| Currently the only way to concatenate `BuiltinString`s is `appendString`, whose cost
 is linear in the total length of the two strings. A naive concatenation of multiple
 `BuiltinString`s costs @O(n^2)@ in the worst case, where @n@ is the total length. By
 collecting the `BuiltinString`s in a list and concatenating them in the end, the cost
 can be reduced to @O(n*logn)@. If we add a @concatStrings@ builtin function in the future,
 the cost can be further reduced to @O(n)@.

 Like `GHC.Show.ShowS`, the purpose of the function type here is to turn list concatenation
 into function composition.
-}
type ShowS = [BuiltinString] -> [BuiltinString]

showString :: BuiltinString -> ShowS
showString = (:)
{-# INLINEABLE showString #-}

showSpace :: ShowS
showSpace = showString " "
{-# INLINEABLE showSpace #-}

showCommaSpace :: ShowS
showCommaSpace = showString ", "
{-# INLINEABLE showCommaSpace #-}

showParen :: Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" . p . showString ")" else p
{-# INLINEABLE showParen #-}

appPrec :: Integer
appPrec = 10
{-# INLINEABLE appPrec #-}

appPrec1 :: Integer
appPrec1 = 11
{-# INLINEABLE appPrec1 #-}

concatBuiltinStrings :: [BuiltinString] -> BuiltinString
concatBuiltinStrings = \case
  [] -> ""
  [x] -> x
  xs ->
    let (ys, zs) = splitAt (length xs `divideInteger` 2) xs
     in concatBuiltinStrings ys `appendString` concatBuiltinStrings zs
{-# INLINEABLE concatBuiltinStrings #-}

{- | Derive `Show` instance. Adapted from @Text.Show.Deriving.deriveShow@.

Note: It requires the OverloadedStrings language extension.
-}
deriveShow :: TH.Name -> TH.Q [TH.Dec]
deriveShow name = do
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
    instanceCxt = TH.AppT (TH.ConT ''Show) <$> tyVars
    instanceType :: TH.Type
    instanceType = TH.AppT (TH.ConT ''Show) $ foldl' TH.AppT (TH.ConT tyConName) tyVars
    showsPrecDecs = deriveShowsPrec cons
  pure <$> TH.instanceD (pure instanceCxt) (pure instanceType) showsPrecDecs

-- | Derive `showsPrec` definition for each data constructor.
deriveShowsPrec :: [TH.ConstructorInfo] -> [TH.Q TH.Dec]
deriveShowsPrec cons =
  [ TH.funD 'showsPrec [clause]
  , -- `showsPrec` must be inlinable for the plugin to inline it
    TH.pragInlD 'showsPrec TH.Inlinable TH.FunLike TH.AllPhases
  ]
 where
  clause = TH.clause [] body []
  body = TH.normalB $ deriveShowsPrecBody cons

deriveShowsPrecBody :: [TH.ConstructorInfo] -> TH.Q TH.Exp
deriveShowsPrecBody cons = do
  p <- TH.newName "_p" -- The precedence argument. It is not always used, hence the leading `_`.
  value <- TH.newName "_value" -- The value to be shown
  let pats = [TH.varP p, TH.varP value]
      body = TH.caseE (TH.varE value) (deriveMatchForCon p <$> cons)
  TH.lamE pats body

-- | Derive `showsPrec` body for a single data constructor.
deriveMatchForCon :: TH.Name -> TH.ConstructorInfo -> TH.Q TH.Match
deriveMatchForCon p = \case
  -- Need a special case for nullary constructors, because
  -- @showParen (_p `greaterThanInteger` 10)@ is not needed for nullary constructors.
  TH.ConstructorInfo
    { TH.constructorName = conName
    , TH.constructorFields = []
    } ->
      TH.match
        (TH.conP conName [])
        (TH.normalB [|showString $(TH.stringE (parenInfixConName conName))|])
        []
  TH.ConstructorInfo
    { TH.constructorName = conName
    , TH.constructorVariant = TH.NormalConstructor
    , TH.constructorFields = argTys@(_ : _)
    }
      | isNonUnitTuple conName -> do
          {- Derive `showsPrec` body for a tuple constructor.
             Example: (,,)
             Output:
               case _value of (,,) arg1 arg2 arg3 ->
                 showString "("
                 . showsPrec 0 arg1 . showString ","
                 . showsPrec 0 arg2 . showString ","
                 . showsPrec 0 arg3 . showString ")"
          -}
          args <-
            for [1 .. length argTys] $ \i ->
              TH.newName ("arg" <> Haskell.show i)

          let showArgExps :: [TH.Q TH.Exp]
              showArgExps = deriveShowExpForArg 0 <$> args
              parenCommaArgExps =
                (TH.varE 'showString `TH.appE` TH.stringE "(")
                  : intersperse (TH.varE 'showString `TH.appE` TH.stringE ",") showArgExps
              mappendArgs =
                Haskell.foldr
                  (`TH.infixApp` TH.varE '(Haskell..))
                  (TH.varE 'showString `TH.appE` TH.stringE ")")
                  parenCommaArgExps
              pats = TH.conP conName (TH.varP <$> args)
              body = TH.normalB mappendArgs
          TH.match pats body []
      | otherwise -> do
          {- Derive `showsPrec` body for a non-tuple constructor.
             Example: C a b
             Output:
               case _value of C arg1 arg2 ->
                 showParen
                   (_p `greaterThanInteger` 10)
                   (showString "C " . showsPrec 11 arg1 . showSpace . showsPrec 11 arg2)
          -}
          args <-
            for [1 .. length argTys] $ \i ->
              TH.newName ("arg" <> Haskell.show i)
          let showArgExps :: [TH.Q TH.Exp]
              showArgExps = deriveShowExpForArg appPrec1 <$> args

              mappendArgs, namedArgs :: TH.Q TH.Exp
              mappendArgs = Haskell.foldr1 alg showArgExps
               where
                alg :: TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp
                alg argExp acc = [|$argExp . showSpace . $acc|]
              namedArgs =
                [|
                  showString
                    $(TH.stringE (parenInfixConName conName <> " "))
                    . $mappendArgs
                  |]
          let pats = TH.conP conName (TH.varP <$> args)
              body =
                TH.normalB
                  [|
                    $(TH.varE 'showParen)
                      ( $(TH.varE p)
                          `greaterThanInteger` $(TH.litE (TH.integerL appPrec))
                      )
                      $namedArgs
                    |]
          TH.match pats body []
  {- Derive `showsPrec` body for a tuple constructor.
     Example: C {c1 ;: a, c2 :: b}
     Output:
       case _value of C arg1 arg2 ->
         showParen
           (_p `greaterThanInteger` 10)
           (showString "C " . showString "{"
              . showString "c1 = " . showsPrec 0 arg1
              . showCommaSpace
              . showString "c2 = " . showsPrec 0 arg2
              . showString "}")
  -}
  TH.ConstructorInfo
    { TH.constructorName = conName
    , TH.constructorVariant = TH.RecordConstructor argNames
    , TH.constructorFields = argTys@(_ : _)
    } -> do
      args <-
        Haskell.traverse
          (\i -> TH.newName ("arg" <> Haskell.show i))
          [1 .. length argTys]
      let showArgExps :: [TH.Q TH.Exp]
          -- The `dropEnd` drops the last comma
          showArgExps = dropEnd 1 $ Haskell.foldMap (uncurry f) (Haskell.zip argNames args)
           where
            f :: TH.Name -> TH.Name -> [TH.Q TH.Exp]
            f argName arg =
              let argNameBase = TH.nameBase argName
                  infixRec =
                    Haskell.showParen
                      (isSym argNameBase)
                      (Haskell.showString argNameBase)
                      ""
               in [ TH.varE 'showString `TH.appE` TH.stringE (infixRec <> " = ")
                  , deriveShowExpForArg 0 arg
                  , TH.varE 'showCommaSpace
                  ]
          braceCommaArgExps = (TH.varE 'showString `TH.appE` TH.stringE "{") : showArgExps
          mappendArgs =
            Haskell.foldr
              (`TH.infixApp` TH.varE '(Haskell..))
              (TH.varE 'showString `TH.appE` TH.stringE "}")
              braceCommaArgExps
          namedArgs =
            [|
              showString $(TH.stringE (parenInfixConName conName <> " "))
                . $mappendArgs
              |]
          pats = TH.conP conName (TH.varP <$> args)
          body =
            TH.normalB
              [|
                showParen
                  ($(TH.varE p) `greaterThanInteger` $(TH.litE (TH.integerL appPrec)))
                  $namedArgs
                |]
      TH.match pats body []
  {- Derive `showsPrec` body for an infix constructor.
     Example: a :+: b, where (:+:) has fixity 9
     Output:
       case _value of argL :+: argR ->
         showParen
           (_p `greaterThanInteger` 9)
           (showsPrec 10 argL . showString " :+: " . showsPrec 10 argR)
  -}
  TH.ConstructorInfo
    { TH.constructorName = conName
    , TH.constructorVariant = TH.InfixConstructor
    } -> do
      al <- TH.newName "argL"
      ar <- TH.newName "argR"
      fi <- fromMaybe TH.defaultFixity <$> TH.reifyFixityCompat conName
      let conPrec = case fi of TH.Fixity prec _ -> Haskell.fromIntegral prec
          opName = TH.nameBase conName
          infixOpE =
            TH.appE (TH.varE 'showString)
              . TH.stringE
              $ if isInfixDataCon opName
                then " " <> opName <> " "
                else " `" <> opName <> "` "
          showArgLExp = deriveShowExpForArg (conPrec + 1) al
          showArgRExp = deriveShowExpForArg (conPrec + 1) ar
          pats = TH.infixP (TH.varP al) conName (TH.varP ar)
          body =
            TH.normalB
              [|
                showParen
                  ($(TH.varE p) `greaterThanInteger` $(TH.litE (TH.integerL conPrec)))
                  ($showArgLExp . $infixOpE . $showArgRExp)
                |]
      TH.match pats body []

-- | Derive the `showsPrec` expression for showing a single constructor argument.
deriveShowExpForArg :: Integer -> TH.Name -> TH.Q TH.Exp
deriveShowExpForArg p tyExpName =
  [|showsPrec p $(TH.varE tyExpName)|]

-- | Add parens if it is an infix data constructor.
parenInfixConName :: TH.Name -> Haskell.String
parenInfixConName conName =
  let conNameBase = TH.nameBase conName
   in Haskell.showParen (isInfixDataCon conNameBase) (Haskell.showString conNameBase) ""
