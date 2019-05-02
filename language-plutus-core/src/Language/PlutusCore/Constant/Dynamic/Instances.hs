-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances
    ( PlcList (..)
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type             (prettyBytes)
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.Function   as Plc
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Sum        as Plc
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Control.Monad.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Char
import           Data.Proxy
import qualified Data.Text                                  as Text
import qualified Data.Text.Prettyprint.Doc                  as Doc
import           GHC.TypeLits

{- Note [Sequencing]
WARNING: it is not allowed to call 'eval' or @readKnown eval@ over a term that already
was 'eval'ed. It may be temptive to preevaluate to WHNF some term if you later need to evaluate
its several instantiations, but it is forbidden to do so. The reason for this restriction is that
'eval' encapsulates its internal state and the state gets updated during evaluation, so if you
try to call 'eval' over something that already was 'eval'ed, that second 'eval' won't have the
updated state that the first 'eval' finished with. This may cause all kinds of weird error messages,
for example, an error message saying that there is a free variable and evaluation cannot proceed.
-}

instance KnownType a => KnownType (EvaluationResult a) where
    toTypeAst _ = toTypeAst @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error () $ toTypeAst @a Proxy
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readKnown' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readKnown eval = mapDeepReflectT (fmap $ EvaluationSuccess . sequence) . readKnown eval

    prettyKnown = pretty . fmap (PrettyConfigIgnore . KnownTypeValue)

instance (KnownSymbol text, KnownNat uniq) => KnownType (OpaqueTerm text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown eval = fmap OpaqueTerm . makeRightReflectT . eval mempty

instance KnownType Integer where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt

    readKnown eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () i) -> pure i
            _                             -> throwError "Not a builtin Integer"

instance KnownType Int where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt . fromIntegral

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            -- TODO: check that 'i' is in bounds.
            Constant () (BuiltinInt () i) -> pure $ fromIntegral i
            _                             -> throwError "Not a builtin Int"

instance KnownType BSL.ByteString where
    toTypeAst _ = TyBuiltin () TyByteString

    makeKnown = Constant () . makeBuiltinBS

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinBS () i) -> pure i
            _                            -> throwError "Not a builtin ByteString"

    prettyKnown = prettyBytes

instance KnownType [Char] where
    toTypeAst _ = TyBuiltin () TyString

    makeKnown = Constant () . makeBuiltinStr

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinStr () s) -> pure s
            _                             -> throwError "Not a builtin String"

instance KnownType Bool where
    toTypeAst _ = bool

    makeKnown b = if b then true else false

    readKnown eval b = do
        let int = TyBuiltin () TyInteger
            asInt = Constant () . BuiltinInt ()
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp () (TyInst () b int) [asInt 1, asInt 0]
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () 1) -> pure True
            Constant () (BuiltinInt () 0) -> pure False
            _                             -> throwError "Not an integer-encoded Bool"

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance KnownType Char where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt . fromIntegral . ord

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () int) -> pure . chr $ fromIntegral int
            _                               -> throwError "Not an integer-encoded Char"

instance KnownType a => KnownType (() -> a) where
    toTypeAst _ = TyFun () unit $ toTypeAst @a Proxy

    -- Note that we can't just prepend a 'LamAbs' to the result due to name shadowing issues.
    makeKnown f =
        Apply () (mkIterInst () Plc.const [da, unit]) $ makeKnown $ f () where
            da = toTypeAst @a Proxy

    readKnown eval df = const <$> readKnown eval (Apply () df unitval)

    prettyKnown f = "\\() ->" Doc.<+> prettyKnown (f ())

makeTypeAndKnown :: forall a. KnownType a => a -> (Type TyName (), Term TyName Name ())
makeTypeAndKnown x = (da, dx) where
    da = toTypeAst @a Proxy
    dx = makeKnown x

instance (KnownType a, KnownType b) => KnownType (a, b) where
    toTypeAst _ =
        mkIterTyApp () (prodN 2)
            [ toTypeAst @a Proxy
            , toTypeAst @b Proxy
            ]

    makeKnown (x, y) = _tupleTerm . runQuote $ getSpineToTuple () [dax, dby] where
        dax = makeTypeAndKnown x
        dby = makeTypeAndKnown y

    readKnown eval dxy = do
        let da = toTypeAst @a Proxy
            db = toTypeAst @b Proxy
            prodNAccessorInst i = mkIterInst () (prodNAccessor 2 i) [da, db]
        -- Read elements of the tuple separately.
        x <- readKnown eval $ Apply () (prodNAccessorInst 0) dxy
        y <- readKnown eval $ Apply () (prodNAccessorInst 1) dxy
        pure (x, y)

    prettyKnown = pretty . bimap KnownTypeValue KnownTypeValue

instance (KnownType a, KnownType b) => KnownType (Either a b) where
    toTypeAst _ =
        mkIterTyApp () Plc.sum
            [ toTypeAst @a Proxy
            , toTypeAst @b Proxy
            ]

    makeKnown s = metaEitherToSum da db ds where
        da = toTypeAst @a Proxy
        db = toTypeAst @b Proxy
        ds = bimap makeKnown makeKnown s

    -- At first I tried this representation:
    --
    -- > ds {(() -> a, () -> b)}
    -- >     (\(x : a) -> (\_ -> x        , \_ -> error {b}))
    -- >     (\(y : b) -> (\_ -> error {a}, \_ -> y        ))
    --
    -- but it didn't work, because here the type of the result always contains both 'a' and 'b',
    -- so values of both of the types are attempted to be extracted via 'readKnown'
    -- which causes a loop when we need to read lists back, because in the nil case we attempt to
    -- read both branches of an 'Either' and one of them is supposed to be a list and the fact
    -- that it's actually an 'Error' does not help, because 'readKnown' is still called
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
    readKnown eval ds = do
        let da = toTypeAst @a Proxy
            db = toTypeAst @b Proxy
            branch = runQuote $ do
                x <- freshName () "x"
                y <- freshName () "y"
                pure $ mkIterApp () (TyInst () ds bool)
                    [ LamAbs () x da true
                    , LamAbs () y db false
                    ]
        isL <- readKnown eval branch
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
            then Left  <$> readKnown eval term
            else Right <$> readKnown eval term

    prettyKnown = either prettyKnown prettyKnown

newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

instance KnownType a => KnownType (PlcList a) where
    toTypeAst _ = TyApp () (_recursiveType listData) $ toTypeAst (Proxy @a)

    makeKnown (PlcList xs) = metaListToList argTy dyns where
        dyns = map makeKnown xs
        argTy = toTypeAst @a Proxy

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
    -- of the list. That is, we implicitly invoke 'readKnown' recursively until the list
    -- is empty.
    readKnown eval list = do
        let term = runQuote $ do
                -- > unwrap list {sum unit (prodN 2 a (list a))} unitval
                -- >     \(x : a) (xs : list a) -> prodNConstructor 2 {a} {list a} x xs
                let listA = toTypeAst @(PlcList a) Proxy
                    a     = toTypeAst @a           Proxy
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
        res <- readKnown eval term
        pure . PlcList $ case res of
            Left  ()              -> []
            Right (x, PlcList xs) -> x : xs

    prettyKnown = pretty . map KnownTypeValue . unPlcList
