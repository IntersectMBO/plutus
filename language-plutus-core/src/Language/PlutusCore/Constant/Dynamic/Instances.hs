{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances
    ( PlcList (..)
    ) where

import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.Function    as Plc
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Sum         as Plc
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type
import           PlutusPrelude                               (forBind)

import           Control.Monad.Except
import           Data.Bitraversable
import           Data.Char
import           Data.Functor
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc

{- Note [Sequencing]
WARNING: it is not allowed to call 'eval' or @readDynamicBuiltin eval@ over a term that already
was 'eval'ed. It may be temptive to preevaluate to WHNF some term if you later need to evaluate
its several instantiations, but it is forbidden to do so. The reason for this restriction is that
'eval' encapsulates its internal state and the state gets updated during evaluation, so if you
try to call 'eval' over something that already was 'eval'ed, that second 'eval' won't have the
updated state that the first 'eval' finished with. This may cause all kinds of weird error messages,
for example, an error message saying that there is a free variable and evaluation cannot proceed.
-}

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (EvaluationResult a) where
    toTypeEncoding _ = toTypeEncoding @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeDynamicBuiltin EvaluationFailure     = pure . Error () $ toTypeEncoding @a Proxy
    makeDynamicBuiltin (EvaluationSuccess x) = makeDynamicBuiltin x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownDynamicBuiltinType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readDynamicBuiltin' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readDynamicBuiltin eval term =
        mapExceptT (EvaluationSuccess . sequence) <$> readDynamicBuiltin eval term

instance KnownDynamicBuiltinType Int where
    toTypeEncoding _ = TyBuiltin () TyInteger

    makeDynamicBuiltin = Just . Constant () . makeBuiltinInt . fromIntegral

    readDynamicBuiltin eval term = do
        res <- eval mempty term
        pure $ lift res >>= \case
            Constant () (BuiltinInt () i) -> pure $ fromIntegral i
            _                               -> throwError "Not a builtin Int"

instance KnownDynamicBuiltinType [Char] where
    toTypeEncoding _ = TyBuiltin () TyString

    makeDynamicBuiltin = pure . Constant () . makeBuiltinStr

    readDynamicBuiltin eval term = do
        res <- eval mempty term
        pure $ lift res >>= \case
            Constant () (BuiltinStr () s) -> pure s
            _                             -> throwError "Not a builtin String"

instance KnownDynamicBuiltinType Bool where
    toTypeEncoding _ = bool

    makeDynamicBuiltin b = pure $ if b then true else false

    readDynamicBuiltin eval b = do
        let int = TyBuiltin () TyInteger
            asInt = Constant () . BuiltinInt ()
        -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
        res <- eval mempty (mkIterApp () (TyInst () b int) [asInt 1, asInt 0])
        pure $ lift res >>= \case
            Constant () (BuiltinInt () 1) -> pure True
            Constant () (BuiltinInt () 0) -> pure False
            _                             -> throwError "Not an integer-encoded Bool"

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance KnownDynamicBuiltinType Char where
    toTypeEncoding _ = TyBuiltin () TyInteger

    makeDynamicBuiltin = Just . Constant () . makeBuiltinInt . fromIntegral . ord

    readDynamicBuiltin eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- eval mempty term
        pure $ lift res >>= \case
            Constant () (BuiltinInt () int) -> pure . chr $ fromIntegral int
            _                               -> throwError "Not an integer-encoded Char"

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (() -> a) where
    toTypeEncoding _ = TyFun () unit $ toTypeEncoding @a Proxy

    -- Note that we can't just prepend a 'LamAbs' to the result due to name shadowing issues.
    makeDynamicBuiltin f =
        fmap (Apply () (mkIterInst () Plc.const [da, unit])) <$> makeDynamicBuiltin $ f () where
            da = toTypeEncoding @a Proxy

    readDynamicBuiltin eval df = fmap const <$> readDynamicBuiltin eval (Apply () df unitval)

makeTypeAndDynamicBuiltin
    :: forall a. KnownDynamicBuiltinType a => a -> Maybe (Type TyName (), Term TyName Name ())
makeTypeAndDynamicBuiltin x = do
    let da = toTypeEncoding @a Proxy
    dx <- makeDynamicBuiltin x
    pure (da, dx)

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (a, b) where
    toTypeEncoding _ =
        mkIterTyApp () (prodN 2)
            [ toTypeEncoding @a Proxy
            , toTypeEncoding @b Proxy
            ]

    makeDynamicBuiltin (x, y) = do
        dax <- makeTypeAndDynamicBuiltin x
        dby <- makeTypeAndDynamicBuiltin y
        pure . _tupleTerm . runQuote $ getSpineToTuple () [dax, dby]

    readDynamicBuiltin eval dxy = do
        let da = toTypeEncoding @a Proxy
            db = toTypeEncoding @b Proxy
            prodNAccessorInst i = mkIterInst () (prodNAccessor 2 i) [da, db]
        -- Read elements of the tuple separately.
        getX <- readDynamicBuiltin eval $ Apply () (prodNAccessorInst 0) dxy
        getY <- readDynamicBuiltin eval $ Apply () (prodNAccessorInst 1) dxy
        pure $ (,) <$> getX <*> getY

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (Either a b) where
    toTypeEncoding _ =
        mkIterTyApp () Plc.sum
            [ toTypeEncoding @a Proxy
            , toTypeEncoding @b Proxy
            ]

    makeDynamicBuiltin s = do
        let da = toTypeEncoding @a Proxy
            db = toTypeEncoding @b Proxy
        ds <- bitraverse makeDynamicBuiltin makeDynamicBuiltin s
        pure $ metaEitherToSum da db ds

    -- At first I tried this representation:
    --
    -- > ds {(() -> a, () -> b)}
    -- >     (\(x : a) -> (\_ -> x        , \_ -> error {b}))
    -- >     (\(y : b) -> (\_ -> error {a}, \_ -> y        ))
    --
    -- but it didn't work, because here the type of the result always contains both 'a' and 'b',
    -- so values of both of the types are attempted to be extracted via 'readDynamicBuiltin'
    -- which causes a loop when we need to read lists back, because in the nil case we attempt to
    -- read both branches of an 'Either' and one of them is supposed to be a list and the fact
    -- that it's actually an 'Error' does not help, because 'readDynamicBuiltin' is still called
    -- recursively where it shouldn't.
    --
    -- So the actual implementation is: first figure out whether the 'sum' is 'left' or 'right' via
    --
    -- > ds {bool} (\(x : a) -> true) (\(y : b) -> false)
    --
    -- and depending on the result call either
    --
    -- > ds {a} (\(x : a) -> x) (\(y : b) -> error {a})
    --
    -- or
    --
    -- > ds {b} (\(x : a) -> error {b}) (\(y : b) -> y)
    readDynamicBuiltin eval ds = do
        let da = toTypeEncoding @a Proxy
            db = toTypeEncoding @b Proxy
            branch = runQuote $ do
                x <- freshName () "x"
                y <- freshName () "y"
                pure $ mkIterApp () (TyInst () ds bool)
                    [ LamAbs () x da true
                    , LamAbs () y db false
                    ]
        getIsL <- readDynamicBuiltin eval branch
        forBind getIsL $ \isL -> do
            let term = runQuote $ do
                    x <- freshName () "x"
                    y <- freshName () "y"
                    pure $ if isL
                        then mkIterApp () (TyInst () ds da)
                            [ LamAbs () x da $ Var () x
                            , LamAbs () y db $ Error () da
                            ]
                        else mkIterApp () (TyInst () ds db)
                            [ LamAbs () x da $ Error () db
                            , LamAbs () y db $ Var () y
                            ]
            if isL
                then fmap Left  <$> readDynamicBuiltin eval term
                else fmap Right <$> readDynamicBuiltin eval term

newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (PlcList a) where
    toTypeEncoding _ = TyApp () (_recursiveType listData) $ toTypeEncoding (Proxy @a)

    makeDynamicBuiltin (PlcList xs) = do
        dyns <- traverse makeDynamicBuiltin xs
        let argTy = toTypeEncoding @a Proxy
        pure $ metaListToList argTy dyns

    -- A natural implementation of this function would be to emit elements of a list one by one
    -- until evaluation of a Plutus Core term finishes. However this approach doesn't scale to other
    -- recursive types, because linear streaming is not suitable for handling tree-like structures.
    -- Another option would be to collect a Haskell value inside a Plutus Core accumulator while
    -- evaluating things on the Plutus Core side. However embedding the entire Haskell into
    -- Plutus Core is a little bit weird and we would need runtime type equality checks
    -- (the simplest way would probably be to use @Dynamic@) or some other trickery.
    -- Here instead we do something very simple: we pattern match in Plutus Core on a list, return
    -- the pieces we got from the pattern match and then recreate the list on the Haskell side.
    -- And that's all.
    -- How a single pattern match can handle a recursive data structure? All of the pieces that we
    -- get from the pattern matching get converted to Haskell and one of those pieces is the tail
    -- of the list. That is, we implicitly invoke 'readDynamicBuiltin' recursively until the list
    -- is empty.
    readDynamicBuiltin eval list = do
        let term = runQuote $ do
                -- > unwrap list {sum unit (prodN 2 a (list a))} unitval
                -- >     \(x : a) (xs : list a) -> prodNConstructor 2 {a} {list a} x xs
                let listA = toTypeEncoding @(PlcList a) Proxy
                    a     = toTypeEncoding @a           Proxy
                    resL = unit
                    resR = mkIterTyApp () (prodN 2) [a, listA]
                    -- TODO: use 'maybe' instead of 'sum'.
                    res  = mkIterTyApp () Plc.sum [resL, resR]
                x  <- freshName () "x"
                xs <- freshName () "xs"
                pure $ mkIterApp () (TyInst () (Unwrap () list) res)
                    [ Apply () (mkIterInst () Plc.left [resL, resR]) unitval
                    ,   LamAbs () x  a
                      . LamAbs () xs listA
                      . Apply () (mkIterInst () Plc.right [resL, resR])
                      $ mkIterApp () (mkIterInst () (prodNConstructor 2) [a, listA])
                          [ Var () x, Var () xs ]
                    ]
        readDynamicBuiltin eval term <&> \conv -> conv <&> \res ->
            PlcList $ case res of
                Left  ()              -> []
                Right (x, PlcList xs) -> x : xs

instance PrettyDynamic a => PrettyDynamic (PlcList a) where
    prettyDynamic = Doc.list . map prettyDynamic . unPlcList
