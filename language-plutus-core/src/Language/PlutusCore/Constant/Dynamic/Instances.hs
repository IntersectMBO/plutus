-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances
    ( TypedTerm (..)
    , Sealed (..)
    , CrossSealed (..)
    , PlcList (..)
    , dynamicSealName
    , dynamicUnsealName
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
import           Language.PlutusCore.StdLib.Data.List       hiding (cons)
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
import           Data.Coerce
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

-- | A wrapper around 'Term' parameterized by a phantom type variable representing the Haskell
-- counterpart of the type of that term.
newtype TypedTerm a = TypedTerm
    { unTypedTerm :: Term TyName Name ()
    }

{- Note [Dynamic builtins as constructors]
We can use dynamic builtins as improvised constructors of data types.
Consider the 'Sealed' example, we have:

1. the hardcoded @sealed@ PLC type of kind @* -> *@
2. the @seal@ dynamic builtin of type @all a. a -> sealed a@
3. the @unseal@ dynamic builtin of type @all a. sealed a -> a@

The Haskell meanings of these things are:

1. 'Sealed' (data type)
2. 'Sealed' (constructor)
3. 'unSealed' (field selector)

I.e.

    seal {Integer} 1

is a value of type @sealed integer@, i.e. @seal@ plays the role of a constructor here,
even though it's really a dynamic builtin.

We immediately run into problems, though. As a dynamic builtin, @seal@ has a meaning and thus
computes. So @seal@ becomes @Sealed@ on the Haskell side, but we also need to go in the other
direction, meaning that @Sealed@ becomes @seal@ back. I.e. the

    seal {Integer} 1

application evaluates to itself, which means that the previous version of the CEK machine was
looping while trying to evaluate that application over and over again. The hack that we added
to handle this is trivial: if an application evaluates to itself, do not attempt to evaluate it
again.

The other difficulty that we have is related to unlifting of values that look like that.
Normally, during evaluation we get one of these:

- an actual constructor (via 'IWrap')
- a ground value (via 'Constant')
- a function (via 'Lam')

We handle all of these in distinct ways, but with dynamic-builtins-as-constructor we have a fourth
option and it's not that clear how to handle it. With 'IWrap' we can apply 'Unwrap' to the term and
compute further thus reducing the size of the term. With 'Constant' we can return it immediately.
With 'Lam' we can apply the term to an argument and compute (so just like with 'IWrap'). But for a
dynamic builtin constructor we can neither return the value immediately, nor reduce it using the
evaluation engine, because the evaluation engine relies on the constant application machinery,
which always unlifts all arguments before passing them to a builtin, and so if unlifting of a value
is required for unlifting of that value, then we have a loop, and thus can't use another dynamic
builtin for unlifting of a dynamic builtin constructor.

It seems, the only thing that we can do here is simply stripping out the constructor syntactically.
But then we're left with a PLC term rather than a Haskell value and can't unlift it further due to
Note [Sequencing]. So what we really need is a dynamic builtin that expects a term that we got
after stripping out the constructor, which allows us to unlift further, because this way we do not
break the evaluation flow anywhere. This is the reason we have 'CrossSealed'. It is a very special
thing: normally `KnownType` connects a PLC type and its corresponding Haskell type, but in this
case we instead change the type while crossing language boundaries: what is sealed on the PLC side,
essentially becomes unsealed (we strip out the constructor) on the Haskell side and in order to
maintain isomorphism between 'readKnown' and 'makeKnown', we are forced to do the exact opposite
in the other direction.

Hence we have

    unseal :: forall a. CrossSealed a -> a

This function does not unseal anything by itself. Instead, it receives something that has already
been unsealed, so the unsealing happens behind the scenes in the @KnownType (CrossSealed a)@
instance.

Now if you think that this is a terrible hack, you haven't seen the actual implementation. There we
patameterize 'CrossSealed' by 'OpaqueTerm' and coerce this monster to 'OpaqueTerm'. But it works.
-}

-- TODO: add a note explaining what that is and why we need it.
newtype Sealed a = Sealed
    { unSealed :: a
    } deriving (Eq, Show)

newtype CrossSealed a = CrossSealed
    { unCrossSealed :: Term TyName Name ()
    }

instance Pretty a => Pretty (Sealed a) where
    pretty (Sealed a) = pretty a

dynamicSealName :: DynamicBuiltinName
dynamicSealName = DynamicBuiltinName "seal"

dynamicSeal :: Term tyname name ()
dynamicSeal = dynamicBuiltinNameAsTerm dynamicSealName

dynamicUnsealName :: DynamicBuiltinName
dynamicUnsealName = DynamicBuiltinName "unseal"

dynamicUnseal :: Term tyname name ()
dynamicUnseal = dynamicBuiltinNameAsTerm dynamicUnsealName

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

instance KnownType a => KnownType (TypedTerm a) where
    toTypeAst _ = toTypeAst @a Proxy

    makeKnown = unTypedTerm

    readKnown eval = fmap TypedTerm . makeRightReflectT . eval mempty

    prettyKnown = pretty . unTypedTerm

-- See Note [Dynamic builtins as constructors].
instance KnownType a => KnownType (Sealed a) where
    toTypeAst _ = TyApp () (TyBuiltin () TySealed) $ toTypeAst @a Proxy

    makeKnown =
        Apply () (TyInst () dynamicSeal $ toTypeAst @a Proxy) . makeKnown . unSealed

    readKnown eval term = fmap Sealed . readKnown eval $ Apply () unseal term where
        unseal = TyInst () dynamicUnseal $ toTypeAst @a Proxy

    prettyKnown (Sealed a) = prettyKnown a

-- See Note [Dynamic builtins as constructors].
instance KnownType a => KnownType (CrossSealed a) where
    toTypeAst _ = toTypeAst @(Sealed a) Proxy

    makeKnown = makeKnown @(Sealed (TypedTerm a)) . coerce

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        -- Syntactically stripping out the constructor.
        case res of
            Apply () (TyInst () cons _) val | cons == dynamicSeal -> pure $ CrossSealed val
            _                                                     -> throwError "Not a sealed value"

    prettyKnown = pretty . unCrossSealed

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
