{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.PlutusCore.Constant.Dynamic.Instances where
--     ( PlcList (..)
--     ) where

import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
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
import           PlutusPrelude                              hiding (bool)
import qualified Language.PlutusCore.MkPlc as Mk
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant.DefaultUni

import           Control.Monad.Except
import           Control.Monad.Morph                         as Morph
import           Control.Monad.Reader
import           Control.Monad.Trans.Compose                 (ComposeT (..))
import           Control.Monad.Trans.Inner
import           Control.Monad.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Char
import           Data.IORef
import           Data.Proxy
import qualified Data.Text                                  as Text
import qualified Data.Text.Prettyprint.Doc                  as Doc
-- import           Data.Typeable
import           GHC.TypeLits
import           Data.Text (Text)
import Data.Typeable

type Evaluable uni =
    ( HasDefaultUni uni
    , GEq uni
    , GShow uni
    , Closed uni
    , uni `Everywhere` Pretty
    , Typeable uni
    )

-- data SomeTypeScheme uni = forall as r. SomeTypeScheme (TypeScheme uni as r)

-- | A thing that evaluates @f@ in monad @m@ and allows to extend the set of
-- dynamic built-in names.
newtype Evaluator f uni m = Evaluator
    { unEvaluator
        :: forall uni'. Evaluable uni'
        => (NameMeaning uni -> NameMeaning uni')
        -> NameMeanings uni'
        -> f TyName Name uni' ()
        -> m (EvaluationResultDef uni')
    }

-- | A computation that runs in @t m@ and has access to an 'Evaluator' that runs in @m@.
-- The idea is that a computation that requires access to an evaluator may introduce new effects
-- even though the underlying evaluator does not have them.
--
-- For example reading of values (see 'readKnownM') runs in 'EvaluateT'
-- (because it needs access to an evaluator) and adds the 'ReflectT' effect on top of that
-- (see the docs of 'ReflectT' for what effects it consists of).
--
-- 'EvaluateT' is a monad transformer transfomer. I.e. it turns one monad transformer
-- into another one.
newtype EvaluateT uni t m a = EvaluateT
    { unEvaluateT :: ReaderT (Evaluator Term uni m) (t m) a
    } deriving
        ( Functor, Applicative, Monad, Alternative, MonadPlus
        , MonadError e
        )

-- | Run an 'EvaluateT' computation using the given 'Evaluator'.
runEvaluateT :: Evaluator Term uni m -> EvaluateT uni t m a -> t m a
runEvaluateT eval (EvaluateT a) = runReaderT a eval

-- | Wrap a computation binding an 'Evaluator' as a 'EvaluateT'.
withEvaluator :: (Evaluator Term uni m -> t m a) -> EvaluateT uni t m a
withEvaluator = EvaluateT . ReaderT

-- | 'thoist' for monad transformer transformers is what 'hoist' for monad transformers.
thoist :: Monad (t m) => (forall b. t m b -> s m b) -> EvaluateT uni t m a -> EvaluateT uni s m a
thoist f (EvaluateT a) = EvaluateT $ Morph.hoist f a

{- Note [Semantics of dynamic built-in types]
We only allow dynamic built-in types that

1. can be represented using static types in PLC. For example Haskell's 'Char' can be represented as
@integer@ in PLC. This restriction makes the dynamic built-in types machinery somewhat similar to
type aliases in Haskell (defined via the @type@ keyword). The reason for this restriction is that
storing values of arbitrary types of a host language in the AST of a target language is commonly far
from being trivial, hence we do not support this right now, but we plan to figure out a way to allow
such extensions to the AST
2. are of kind @*@. Dynamic built-in types that are not of kind @*@ can be encoded via recursive
instances. For example:

    instance KnownType a => KnownType [a] where
        ...

The meaning of a free type variable is 'OpaqueTerm'.

This is due to the fact that we use Haskell classes to assign semantics to dynamic built-in types and
since it's anyway impossible to assign a meaning to an open PLC type, because you'd have to somehow
interpret free variables, we're only interested in closed PLC types and those can be handled by
recursive instances as shown above.

Since type classes are globally coherent by design, we also have global coherence for dynamic built-in
types for free. Any dynamic built-in type means the same thing regardless of the blockchain it's
added to. It may prove to be restrictive, but it's a good property to start with, because less things
can silently stab you in the back.

An @KnownType a@ instance provides

1. a way to encode @a@ as a PLC type ('toTypeAst')
2. a function that encodes values of type @dyn@ as PLC terms ('makeKnown')
3. a function that decodes PLC terms back to Haskell values ('readKnown')

The last two are ought to constitute an isomorphism.
-}

{- Note [Converting PLC values to Haskell values]
The first thought that comes to mind when you asked to convert a PLC value to the corresponding Haskell
value is "just match on the AST". This works nicely for simple things like 'Char's which we encode as
@integer@s, see the @KnownType Char@ instance.

But how to convert something more complicated like lists? A PLC list gets passed as argument to
a built-in after it gets evaluated to WHNF. We can't just match on the AST here, because after
the initial lambda it can be anything there: function applications, other built-ins, recursive data,
anything. "Well, just normalize it" -- not so fast: for one, we did not have a term normalization
procedure at the moment this note was written, for two, it's not something that can be easily done,
because you have to carefully handle uniques (we generate new terms during evaluation) and perform
type substitutions, because types must be preserved.

Besides, matching on the AST becomes really complicated: you have to ensure that a term does have
an expected semantics by looking at the term's syntax. Huge pattern matches followed by multiple
checks that variables have equal names in right places and have distinct names otherwise. Making a
mistake is absolutely trivial here. Of course, one could just omit checks and hope it'll work alright,
but eventually it'll break and debugging won't be fun at all.

So instead of dealing with syntax of terms, we deal with their semantics. Namely, we evaluate terms
using some evaluator (normally, the CEK machine). For the temporary lack of ability to put values of
arbitrary Haskell types into the Plutus Core AST, we have some ad hoc strategies for converting PLC
values to Haskell values (ground, product, sum and recursive types are all handled distinctly,
see the "Language.PlutusCore.Constant.Dynamic.Instances" module).
-}

{- Note [Evaluators]
A dynamic built-in name can be applied to something that contains uninstantiated variables. There are
several possible ways to handle that:

1. each evaluator is required to perform substitutions to instantiate all variables in arguments to
built-ins. The drawback is that this can be inefficient in cases when there are many applications of
built-ins and arguments are of non-primitive types. Besides, substitution is tricky and is trivial to
screw up
2. we can break encapsulation and pass environments to the built-ins application machinery, so that it
knows how to instantiate variables. This would work for the strict CEK machine, but the lazy
CEK machine also has a heap and there can be other evaluators that have their internal state that
can't just be thrown away and it's impossible for the built-ins application machinery to handle states
of all possible evaluators beforehand
3. or we can just require to pass the current evaluator with its encapsulated state to functions that
evaluate built-in applications. The type of evaluators is this then:

    type Evaluator f m = NameMeanings -> f TyName Name () -> m EvaluationResult

so @Evaluator Term uni m@ receives a map with meanings of dynamic built-in names which extends the map the
evaluator already has (this is needed, because we may add new dynamic built-in names during conversion
of PLC values to Haskell values), a 'Term' to evaluate and returns an @m EvaluationResult@.
Thus, whenever we want to resume evaluation during computation of a dynamic built-in application,
we just call the received evaluator

(3) seems best, so it's what is implemented.
-}

-- | The monad in which we convert PLC terms to Haskell values.
-- Conversion can fail with
--
-- 1. 'EvaluationFailure' if evaluation fails with @error@.
-- 2. A textual error if a PLC term can't be converted to a Haskell value of a specified type.
newtype ReflectT m a = ReflectT
    { unReflectT :: ExceptT Text (InnerT EvaluationResult m) a
    } deriving
        ( Functor, Applicative, Monad
        , MonadError Text
        )
      deriving MonadTrans via ComposeT (ExceptT Text) (InnerT EvaluationResult)

-- Uses the 'Alternative' instance of 'EvaluationResult'.
instance Monad m => Alternative (ReflectT m) where
    empty = ReflectT . lift $ yield empty
    ReflectT (ExceptT (InnerT m)) <|> ReflectT (ExceptT (InnerT n)) =
        ReflectT . ExceptT . InnerT $ (<|>) <$> m <*> n

-- | Run a 'ReflectT' computation.
runReflectT :: ReflectT m a -> m (EvaluationResult (Either Text a))
runReflectT = unInnerT . runExceptT . unReflectT

-- | Map over the underlying representation of 'ReflectT'.
mapReflectT
    :: (ExceptT Text (InnerT EvaluationResult m) a -> ExceptT Text (InnerT EvaluationResult n) b)
    -> ReflectT m a
    -> ReflectT n b
mapReflectT f (ReflectT a) = ReflectT (f a)

-- | Map over the fully unwrapped underlying representation of a 'ReflectT' computation.
mapDeepReflectT
    :: (m (EvaluationResult (Either Text a)) -> n (EvaluationResult (Either Text b)))
    -> ReflectT m a
    -> ReflectT n b
mapDeepReflectT = mapReflectT . mapExceptT . mapInnerT

-- | Fully wrap a computation into 'ReflectT'.
makeReflectT :: m (EvaluationResult (Either Text a)) -> ReflectT m a
makeReflectT = ReflectT . ExceptT . InnerT

-- | Wrap a non-throwing computation into 'ReflectT'.
makeRightReflectT :: Monad m => m (EvaluationResult a) -> ReflectT m a
makeRightReflectT = ReflectT . lift . InnerT

-- See Note [Semantics of dynamic built-in types].
-- See Note [Converting PLC values to Haskell values].
-- | Haskell types known to exist on the PLC side.
class PrettyKnown a => KnownType a uni where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName uni ()

    -- | Convert a Haskell value to the corresponding PLC value.
    makeKnown :: a -> Term TyName Name uni ()

    -- See Note [Evaluators].
    -- | Convert a PLC value to the corresponding Haskell value using an explicit evaluator.
    readKnown :: Monad m => Evaluator Term uni m -> Term TyName Name uni () -> ReflectT m a

class PrettyKnown a where
    -- | Pretty-print a value of a 'KnownType' in a PLC-specific way
    -- (see e.g. the @ByteString@ instance).
    prettyKnown :: a -> Doc ann
    default prettyKnown :: Pretty a => a -> Doc ann
    prettyKnown = pretty

-- | Convert a PLC value to the corresponding Haskell value using the evaluator
-- from the current context.
readKnownM
    :: (Monad m, KnownType a uni)
    => Term TyName Name uni () -> EvaluateT uni ReflectT m a
readKnownM term = withEvaluator $ \eval -> readKnown eval term

-- | A value that is supposed to be of a 'KnownType'. Needed in order to give a 'Pretty' instance
-- for any 'KnownType' via 'prettyKnown', which allows e.g. to pretty-print a list of 'KnownType'
-- values using the standard 'pretty' pretty-printer for the shape of the list and our specific
-- 'prettyKnown' pretty-printer for the elements of the list.
newtype KnownTypeValue a = KnownTypeValue
    { unKnownTypeValue :: a
    }

instance PrettyKnown a => Pretty (KnownTypeValue a) where
    pretty = prettyKnown . unKnownTypeValue

{- Note [The reverse example]
Having a dynamic built-in with the following signature:

    reverse : all a. list a -> list a

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [OpaqueTerm true, OpaqueTerm false])
    ~ makeKnown [OpaqueTerm false, OpaqueTerm true]
    ~ cons false (cons true nil)

Note how we use 'OpaqueTerm' in order to wrap a PLC term as a Haskell value using 'readKnown' and
then unwrap the term back using 'makeKnown' without ever inspecting the term.
-}

{- Note [Sequencing]
WARNING: it is not allowed to call 'eval' or @readKnown eval@ over a term that already
was 'eval'ed. It may be temptive to preevaluate to WHNF some term if you later need to evaluate
its several instantiations, but it is forbidden to do so. The reason for this restriction is that
'eval' encapsulates its internal state and the state gets updated during evaluation, so if you
try to call 'eval' over something that already was 'eval'ed, that second 'eval' won't have the
updated state that the first 'eval' finished with. This may cause all kinds of weird error messages,
for example, an error message saying that there is a free variable and evaluation cannot proceed.
-}

shiftEvaluator :: Evaluator f uni m -> Evaluator f (Extend b uni) m
shiftEvaluator (Evaluator eval) =
    Evaluator $ \emb means -> eval (emb . shiftNameMeaning) means

unshiftEvaluator :: Evaluator f (Extend b uni) m -> Evaluator f uni m
unshiftEvaluator (Evaluator eval) =
    Evaluator $ \emb means -> eval (emb . unshiftNameMeaning) means

-- Encode '()' from Haskell as @all r. r -> r@ from PLC.
-- This is a very special instance, because it's used to define functions that are needed for
-- other instances, so we keep it here.
instance Evaluable uni => KnownType () uni where
    toTypeAst _ = unit

    -- We need this matching, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' for logging, so we want to compute the '()' just
    -- for side effects that the evaluation may cause.
    makeKnown () = unitval

    readKnown (Evaluator eval) term = do
        let metaUnit = Mk.extensionType ()
            metaUnitval = Mk.extensionTerm () ()
            applied = Apply () (TyInst () (shiftConstantsTerm term) metaUnit) metaUnitval
        res <- makeRightReflectT $ eval shiftNameMeaning mempty applied
        case extractExtension res of
            Just () -> pure ()
            Nothing -> throwError "Not a builtin ()"
instance PrettyKnown ()

instance KnownType a uni => KnownType (EvaluationResult a) uni where
    toTypeAst _ = toTypeAst @a Proxy

    makeKnown EvaluationFailure     = Error () $ toTypeAst @a Proxy
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readKnown' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readKnown eval = mapDeepReflectT (fmap $ EvaluationSuccess . sequence) . readKnown eval
instance PrettyKnown a => PrettyKnown (EvaluationResult a) where
    prettyKnown = pretty . fmap (PrettyConfigIgnore . KnownTypeValue)

instance (KnownSymbol text, KnownNat uniq, uni1 ~ uni2, Evaluable uni1) =>
            KnownType (OpaqueTerm uni2 text uniq) uni1 where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown (Evaluator eval) = fmap OpaqueTerm . makeRightReflectT . eval id mempty
instance PrettyKnown (OpaqueTerm uni text uniq) where
    prettyKnown = undefined

instance Evaluable uni => KnownType Integer uni where
    toTypeAst _ = constantType @Integer Proxy ()

    makeKnown = constantTerm ()

    readKnown (Evaluator eval) term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            Just i  -> pure i
            Nothing -> throwError "Not a builtin Integer"
instance PrettyKnown Integer

instance Evaluable uni => KnownType Int uni where
    toTypeAst _ = constantType @Integer Proxy ()

    makeKnown = constantTerm @Integer () . fromIntegral

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            -- TODO: check that 'i' is in bounds.
            Just i -> pure $ fromIntegral @Integer i
            _      -> throwError "Not a builtin Int"
instance PrettyKnown Int

instance Evaluable uni => KnownType BSL.ByteString uni where
    toTypeAst _ = constantType @BSL.ByteString Proxy ()

    makeKnown = constantTerm ()

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            Just bs -> pure bs
            Nothing -> throwError "Not a builtin ByteString"
instance PrettyKnown BSL.ByteString where
    prettyKnown = prettyBytes

instance Evaluable uni => KnownType [Char] uni where
    toTypeAst _ = constantType @String Proxy ()

    makeKnown = constantTerm ()

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            Just s  -> pure s
            Nothing -> throwError "Not a builtin String"
instance PrettyKnown [Char]

instance Evaluable uni => KnownType Bool uni where
    toTypeAst _ = bool

    makeKnown b = if b then true else false

    readKnown (Evaluator eval) term = do
        let metaBool  = extensionType ()
            metaTrue  = extensionTerm () True
            metaFalse = extensionTerm () False
            applied =
                mkIterApp () (TyInst () (shiftConstantsTerm term) metaBool)
                    [metaTrue, metaFalse]
        res <- makeRightReflectT $ eval shiftNameMeaning mempty applied
        case extractExtension res of
            Just b  -> pure b
            Nothing -> throwError "Not a Bool"
instance PrettyKnown Bool

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance Evaluable uni => KnownType Char uni where
    toTypeAst _ = constantType @Integer Proxy ()

    makeKnown = constantTerm @Integer () . fromIntegral . ord

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            Just i -> pure . chr $ fromIntegral @Integer i
            _      -> throwError "Not an integer-encoded Char"
instance PrettyKnown Char

instance KnownType a uni => KnownType (() -> a) uni where
    toTypeAst _ = TyFun () unit $ toTypeAst @a Proxy

    -- Note that we can't just prepend a 'LamAbs' to the result due to name shadowing issues.
    makeKnown f =
        Apply () (mkIterInst () Plc.const [da, unit]) $ makeKnown $ f () where
            da = toTypeAst @a Proxy

    readKnown eval df = const <$> readKnown eval (Apply () df unitval)
instance PrettyKnown a => PrettyKnown (() -> a) where
    prettyKnown f = "\\() ->" Doc.<+> prettyKnown (f ())

makeTypeAndKnown
    :: forall uni a. KnownType a uni => a -> (Type TyName uni (), Term TyName Name uni ())
makeTypeAndKnown x = (da, dx) where
    da = toTypeAst @a Proxy
    dx = makeKnown x

data Meta a = Meta
    { unMeta :: a
    } deriving (Show, Generic, Typeable)

-- TODO: derive all the 'Integer', 'ByteString' and other instances in term of this one.
instance (Evaluable uni, uni `Includes` a) => KnownType (Meta a) uni where
    toTypeAst _ = constantType @a Proxy ()

    makeKnown (Meta x) = constantTerm () x

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractValue res of
            Just x -> pure $ Meta x
            _      -> throwError "Not an integer-encoded Char"
instance PrettyKnown (Meta a) where
    prettyKnown = undefined

newtype InExtended (b :: *) (uni :: * -> *) a = InExtended
    { unInExtended :: a
    }

-- A type known in a universe is known in an extended version of that universe.
instance (Evaluable uni, KnownType a uni, euni ~ Extend b uni) =>
            KnownType (InExtended b uni a) euni where
    toTypeAst _ = shiftConstantsType $ toTypeAst @a @uni Proxy

    makeKnown (InExtended x) = shiftConstantsTerm $ makeKnown @a x

    readKnown eval term =
        InExtended <$> readKnown @a (unshiftEvaluator eval) (unshiftConstantsTerm term)

instance PrettyKnown (InExtended b uni a) where
    prettyKnown = Prelude.error "ololo1"

newtype InUnextended (euni :: * -> *) a = InUnextended
    { unInUnextended :: a
    }

instance (Evaluable uni, KnownType a euni, euni ~ Extend b uni) =>
            KnownType (InUnextended euni a) uni where
    toTypeAst _ = unshiftConstantsType $ toTypeAst @a @euni Proxy

    makeKnown (InUnextended x) = unshiftConstantsTerm $ makeKnown @a @euni x

    readKnown eval term =
        InUnextended <$> readKnown @a @euni (shiftEvaluator eval) (shiftConstantsTerm term)

instance PrettyKnown (InUnextended euni a) where
    prettyKnown = Prelude.error "ololo1"

newtype AsExtension (uni :: * -> *) a = AsExtension
    { unAsExtension :: a
    }

instance (Evaluable uni, euni ~ Extend a uni, Typeable a, Pretty a) =>
            KnownType (AsExtension uni a) euni where
    toTypeAst _ = extensionType ()

    makeKnown = extensionTerm () . unAsExtension

    readKnown (Evaluator eval) term = do
        res <- makeRightReflectT $ eval id mempty term
        case extractExtension res of
            Just x -> pure $ AsExtension x
            _      -> throwError "Not an integer-encoded Char"
instance PrettyKnown (AsExtension uni a) where
    prettyKnown = Prelude.error "ololo2"

instance (Evaluable uni, KnownType a uni, KnownType b uni, Typeable a, Typeable b, Pretty a, Pretty b) =>
            KnownType (a, b) uni where
    toTypeAst _ =
        mkIterTyApp () (prodN 2)
            [ toTypeAst @a Proxy
            , toTypeAst @b Proxy
            ]

    makeKnown (x, y) = _tupleTerm . runQuote $ getSpineToTuple () [dax, dby] where
        dax = makeTypeAndKnown x
        dby = makeTypeAndKnown y

    readKnown (Evaluator eval) term = do
        let metaTuple = extensionType ()
            metaCommaName = DynamicBuiltinName $ fold
                [ "comma_"
                , showText $ typeRep (Proxy :: Proxy a)
                , "_"
                , showText $ typeRep (Proxy :: Proxy b)
                ]

-- convert :: Term TyName Name uni () -> Term TyName Name (Extend b uni) ()

-- (,) :: Integer -> Bool -> (Integer, Bool)

-- readKnown :: Monad m => Evaluator Term uni m -> Term TyName Name uni () -> ReflectT m a

            metaCommaMeaning :: NameMeaning (Extend (a, b) (Extend b (Extend a uni)))
            metaCommaMeaning = NameMeaning sch (,) where
                sch =
                    TypeGroundValue (Original $ Original Extension) `TypeSchemeArrow`
                    TypeGroundValue (Original Extension) `TypeSchemeArrow`
                    TypeSchemeResult (TypeGroundValue Extension)

            metaCommaDef = NameDefinition metaCommaName metaCommaMeaning
            metaComma = dynamicBuiltinNameAsTerm metaCommaName

            env = insertNameDefinition metaCommaDef mempty
            applied = Apply () (TyInst () (substConstantsTerm (Original . Original . Original) term) metaTuple) metaComma
        res <- makeRightReflectT $ eval (shiftNameMeaning . shiftNameMeaning . shiftNameMeaning) env applied
        case extractExtension res of
            Just p  -> pure p
            Nothing -> throwError $ "Not a builtin tuple: " <> prettyText applied

    -- readKnown (Evaluator eval) term = do
    --     let metaTuple = extensionType ()
    --         metaCommaName = DynamicBuiltinName $ fold
    --             [ "comma_"
    --             , showText $ typeRep (Proxy :: Proxy a)
    --             , "_"
    --             , showText $ typeRep (Proxy :: Proxy b)
    --             ]

    --         metaCommaMeaning :: NameMeaning (Extend (a, b) uni)
    --         metaCommaMeaning = NameMeaning sch def where
    --             sch =
    --                 Proxy @(InExtended (a, b) uni a) `TypeSchemeArrow`
    --                 Proxy @(InExtended (a, b) uni b) `TypeSchemeArrow`
    --                 TypeSchemeResult (Proxy @(AsExtension uni (a, b)))
    --             def (InExtended x) (InExtended y) = AsExtension (x, y)

    --         metaCommaDef = NameDefinition metaCommaName metaCommaMeaning
    --         metaComma = dynamicBuiltinNameAsTerm metaCommaName

    --         env = insertNameDefinition metaCommaDef mempty
    --         applied = Apply () (TyInst () (shiftConstantsTerm term) metaTuple) metaComma
    --     res <- makeRightReflectT $ eval shiftNameMeaning env applied
    --     case extractExtension res of
    --         Just p  -> pure p
    --         Nothing -> throwError $ "Not a builtin tuple: " <> prettyText applied

instance (PrettyKnown a, PrettyKnown b) => PrettyKnown (a, b) where
    prettyKnown = pretty . bimap KnownTypeValue KnownTypeValue

-- instance (KnownType a, KnownType b) => KnownType (Either a b) where
--     toTypeAst _ =
--         mkIterTyApp () Plc.sum
--             [ toTypeAst @a Proxy
--             , toTypeAst @b Proxy
--             ]

--     makeKnown s = metaEitherToSum da db ds where
--         da = toTypeAst @a Proxy
--         db = toTypeAst @b Proxy
--         ds = bimap makeKnown makeKnown s

--     -- At first I tried this representation:
--     --
--     -- > ds {(() -> a, () -> b)}
--     -- >     (\(x : a) -> (\_ -> x        , \_ -> error {b}))
--     -- >     (\(y : b) -> (\_ -> error {a}, \_ -> y        ))
--     --
--     -- but it didn't work, because here the type of the result always contains both 'a' and 'b',
--     -- so values of both of the types are attempted to be extracted via 'readKnown'
--     -- which causes a loop when we need to read lists back, because in the nil case we attempt to
--     -- read both branches of an 'Either' and one of them is supposed to be a list and the fact
--     -- that it's actually an 'Error' does not help, because 'readKnown' is still called
--     -- recursively where it shouldn't.
--     --
--     -- So the actual implementation is: first figure out whether the 'sum' is 'left' or 'right' via
--     --
--     -- > ds {bool} (\(x : a) -> true) (\(y : b) -> false)
--     --
--     -- and depending on the result call either
--     --
--     -- > ds {a} (\(x : a) -> x) (\(y : b) -> error {a})
--     --
--     -- or
--     --
--     -- > ds {b} (\(x : a) -> error {b}) (\(y : b) -> y)
--     readKnown eval ds = do
--         let da = toTypeAst @a Proxy
--             db = toTypeAst @b Proxy
--             branch = runQuote $ do
--                 x <- freshName () "x"
--                 y <- freshName () "y"
--                 pure $ mkIterApp () (TyInst () ds bool)
--                     [ LamAbs () x da true
--                     , LamAbs () y db false
--                     ]
--         isL <- readKnown eval branch
--         let term = runQuote $ do
--                 x <- freshName () "x"
--                 y <- freshName () "y"
--                 pure $ if isL
--                     then mkIterApp () (TyInst () ds da)
--                         [ LamAbs () x da $ Var () x
--                         , LamAbs () y db $ Error () da
--                         ]
--                     else mkIterApp () (TyInst () ds db)
--                         [ LamAbs () x da $ Error () db
--                         , LamAbs () y db $ Var () y
--                         ]
--         if isL
--             then Left  <$> readKnown eval term
--             else Right <$> readKnown eval term

--     prettyKnown = either prettyKnown prettyKnown

-- newtype PlcList a = PlcList
--     { unPlcList :: [a]
--     } deriving (Eq, Show)

-- instance KnownType a => KnownType (PlcList a) where
--     toTypeAst _ = TyApp () (_recursiveType listData) $ toTypeAst (Proxy @a)

--     makeKnown (PlcList xs) = metaListToList argTy dyns where
--         dyns = map makeKnown xs
--         argTy = toTypeAst @a Proxy

--     -- A natural implementation of this function would be to emit elements of a list one by one
--     -- until evaluation of a Plutus Core term finishes. However this approach doesn't scale to other
--     -- recursive types, because linear streaming is not suitable for handling tree-like structures.
--     -- Another option would be to collect a Haskell value inside a Plutus Core accumulator while
--     -- evaluating things on the Plutus Core side. However embedding the entire Haskell into
--     -- Plutus Core is a little bit weird and we would need runtime type equality checks
--     -- (the simplest way would probably be to use @Dynamic@) or some other trickery.
--     -- Here instead we do something very simple: we pattern match in Plutus Core on a list, return
--     -- the pieces we got from the pattern match and then recreate the list on the Haskell side.
--     -- And that's all.
--     -- How a single pattern match can handle a recursive data structure? All of the pieces that we
--     -- get from the pattern matching get converted to Haskell and one of those pieces is the tail
--     -- of the list. That is, we implicitly invoke 'readKnown' recursively until the list
--     -- is empty.
--     readKnown eval list = do
--         let term = runQuote $ do
--                 -- > unwrap list {sum unit (prodN 2 a (list a))} unitval
--                 -- >     \(x : a) (xs : list a) -> prodNConstructor 2 {a} {list a} x xs
--                 let listA = toTypeAst @(PlcList a) Proxy
--                     a     = toTypeAst @a           Proxy
--                     resL = unit
--                     resR = mkIterTyApp () (prodN 2) [a, listA]
--                     -- TODO: use 'maybe' instead of 'sum'.
--                     res  = mkIterTyApp () Plc.sum [resL, resR]
--                 x  <- freshName () "x"
--                 xs <- freshName () "xs"
--                 pure $ mkIterApp () (TyInst () (Unwrap () list) res)
--                     [ Apply () (mkIterInst () Plc.left [resL, resR]) unitval
--                     ,   LamAbs () x  a
--                       . LamAbs () xs listA
--                       . Apply () (mkIterInst () Plc.right [resL, resR])
--                       $ mkIterApp () (mkIterInst () (prodNConstructor 2) [a, listA])
--                           [ Var () x, Var () xs ]
--                     ]
--         res <- readKnown eval term
--         pure . PlcList $ case res of
--             Left  ()              -> []
--             Right (x, PlcList xs) -> x : xs

--     prettyKnown = pretty . map KnownTypeValue . unPlcList
