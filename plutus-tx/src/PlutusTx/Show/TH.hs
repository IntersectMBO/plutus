{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module PlutusTx.Show.TH where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins hiding (showString)
import PlutusTx.Foldable
import PlutusTx.List

import Data.Deriving.Internal (isInfixDataCon, isNonUnitTuple, isSym, varTToName)
import Data.List.Extra (dropEnd, foldl', intersperse)
import Data.Maybe
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import Prelude (pure, (+), (<$>), (<>))
import Prelude qualified as Haskell

{- | Conversion of values to `BuiltinString`s. Unlike @GHC.Show.Show@, there is no
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

{- | Currently the only way to concatenate `BuiltinString`s is `appendString`, whose cost
 is linear in the total length of the two strings. A naive concatenation of multiple
 `BuiltinString`s costs @O(n^2)@ in the worst case, where @n@ is the total length. By
 collecting the `BuiltinString`s in a list and concatenating them in the end, the cost
 can be reduced to @O(n*logn)@. If we add a @concatStrings@ builtin function in the future,
 the cost can be further reduced to @O(n)@.

 Like `GHC.Show.ShowS`, the purpose of the function type here is to turn list concatenation
 into function composition.
-}
type ShowS = [BuiltinString] -> [BuiltinString]

{-# INLINEABLE showString #-}
showString :: BuiltinString -> ShowS
showString = (:)

{-# INLINEABLE showSpace #-}
showSpace :: ShowS
showSpace = showString " "

{-# INLINEABLE showCommaSpace #-}
showCommaSpace :: ShowS
showCommaSpace = showString ", "

{-# INLINEABLE showParen #-}
showParen :: Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" . p . showString ")" else p

{-# INLINEABLE appPrec #-}
appPrec :: Integer
appPrec = 10

{-# INLINEABLE appPrec1 #-}
appPrec1 :: Integer
appPrec1 = 11

{-# INLINEABLE concatBuiltinStrings #-}
concatBuiltinStrings :: [BuiltinString] -> BuiltinString
concatBuiltinStrings = \case
    [] -> ""
    [x] -> x
    xs ->
        let (ys, zs) = splitAt (length xs `divideInteger` 2) xs
         in concatBuiltinStrings ys `appendString` concatBuiltinStrings zs

-- | Derive `Show` instance. Adapted from @Text.Show.Deriving.deriveShow@.
deriveShow :: TH.Name -> TH.DecsQ
deriveShow name = do
    TH.DatatypeInfo
        { TH.datatypeName = tyConName
        , TH.datatypeInstTypes = tyVars0
        , TH.datatypeCons = cons
        } <-
        TH.reifyDatatype name
    let -- The purpose of the `TH.VarT . varTToName` roundtrip is to remove the kind
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
deriveShowsPrec :: [TH.ConstructorInfo] -> [TH.DecQ]
deriveShowsPrec cons =
    [ TH.funD 'showsPrec [clause]
    , -- `showsPrec` must be inlinable for the plugin to inline it
      TH.pragInlD 'showsPrec TH.Inlinable TH.FunLike TH.AllPhases
    ]
  where
    clause = TH.clause [] body []
    body = TH.normalB $ deriveShowsPrecBody cons

deriveShowsPrecBody :: [TH.ConstructorInfo] -> TH.ExpQ
deriveShowsPrecBody cons = do
    p <- TH.newName "_p" -- The precedence argument. It is not always used, hence the leading `_`.
    value <- TH.newName "_value" -- The value to be shown
    let pats = [TH.varP p, TH.varP value]
        body = TH.caseE (TH.varE value) (deriveMatchForCon p <$> cons)
    TH.lamE pats body

{- | Derive `showsPrec` body for a single data constructor.

 Example: given `C Integer Bool`, this generates

 @
    case _value of C arg1 arg2 ->
        showParen
            (_p `greaterThanInteger` 10)
            (showString "C " . showsPrec 11 arg1 . showSpace . showsPrec 11 arg2)
 @
-}
deriveMatchForCon :: TH.Name -> TH.ConstructorInfo -> TH.MatchQ
deriveMatchForCon p = \case
    TH.ConstructorInfo
        { TH.constructorName = conName
        , TH.constructorFields = []
        } ->
            TH.match
                (TH.conP conName [])
                (TH.normalB [| showString  $(TH.stringE (parenInfixConName conName))|])
                []
    TH.ConstructorInfo
        { TH.constructorName = conName
        , TH.constructorVariant = TH.NormalConstructor
        , TH.constructorFields = argTys@(_ : _)
        } -> do
            args <-
                Haskell.traverse
                    (\i -> TH.newName ("arg" <> Haskell.show i))
                    [1 .. length argTys]

            if isNonUnitTuple conName
                then do
                    let showArgExps :: [TH.ExpQ]
                        showArgExps = deriveShowExpForArg 0 <$> args
                        parenCommaArgExps =
                            (TH.varE 'showString `TH.appE` TH.stringE "(") :
                            intersperse (TH.varE 'showString `TH.appE` TH.stringE ",") showArgExps
                        mappendArgs =
                            Haskell.foldr
                                (`TH.infixApp` TH.varE '(Haskell..))
                                (TH.varE 'showString `TH.appE` TH.stringE ")")
                                parenCommaArgExps
                        pats = TH.conP conName (TH.varP <$> args)
                        body = TH.normalB mappendArgs
                    TH.match pats body []
                else do
                    let showArgExps :: [TH.ExpQ]
                        showArgExps = deriveShowExpForArg appPrec1 <$> args

                        mappendArgs, namedArgs :: TH.ExpQ
                        mappendArgs = Haskell.foldr1 alg showArgExps
                          where
                            alg :: TH.ExpQ -> TH.ExpQ -> TH.ExpQ
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
    TH.ConstructorInfo
        { TH.constructorName = conName
        , TH.constructorVariant = TH.RecordConstructor argNames
        , TH.constructorFields = argTys@(_ : _)
        } -> do
            args <-
                Haskell.traverse
                    (\i -> TH.newName ("arg" <> Haskell.show i))
                    [1 .. length argTys]
            let showArgExps :: [TH.ExpQ]
                -- The `dropEnd` drops the last comma
                showArgExps = dropEnd 1 $ Haskell.foldMap (uncurry f) (Haskell.zip argNames args)
                  where
                    f :: TH.Name -> TH.Name -> [TH.ExpQ]
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
                        $(TH.varE 'showString) $(TH.stringE (parenInfixConName conName <> " "))
                            . $mappendArgs
                        |]
                pats = TH.conP conName (TH.varP <$> args)
                body =
                    TH.normalB
                        [|
                            $(TH.varE 'showParen)
                                ($(TH.varE p) `greaterThanInteger` $(TH.litE (TH.integerL appPrec)))
                                $namedArgs
                            |]
            TH.match pats body []
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
                    TH.appE (TH.varE 'showString) . TH.stringE $
                        if isInfixDataCon opName
                            then " " <> opName <> " "
                            else " `" <> opName <> "` "
                showArgLExp = deriveShowExpForArg (conPrec + 1) al
                showArgRExp = deriveShowExpForArg (conPrec + 1) ar
                pats = TH.infixP (TH.varP al) conName (TH.varP ar)
                body =
                    TH.normalB
                        [|
                            $(TH.varE 'showParen)
                                ($(TH.varE p) `greaterThanInteger` $(TH.litE (TH.integerL conPrec)))
                                ($showArgLExp . $infixOpE . $showArgRExp)
                            |]
            TH.match pats body []

deriveShowExpForArg :: Integer -> TH.Name -> TH.ExpQ
deriveShowExpForArg p tyExpName =
    [|$(TH.varE 'showsPrec) $(TH.litE (TH.integerL p)) $(TH.varE tyExpName)|]

-- | Add parens if it is an infix data constructor.
parenInfixConName :: TH.Name -> Haskell.String
parenInfixConName conName =
    let conNameBase = TH.nameBase conName
     in Haskell.showParen (isInfixDataCon conNameBase) (Haskell.showString conNameBase) ""
