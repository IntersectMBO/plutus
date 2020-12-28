-- GHC doesn't like the definition of 'toDynamicBuiltinMeaning'.
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.PlutusCore.Constant.Meaning where

import           PlutusPrelude

import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Lens                                     (ix, (^?))
import           Control.Monad.Except
import           Data.Array
import qualified Data.Kind                                        as GHC
import           Data.Proxy
import           GHC.TypeLits

-- | The meaning of a dynamic built-in function consists of its type represented as a 'TypeScheme',
-- its Haskell denotation and a costing function (both in uninstantiated form).
--
-- The 'TypeScheme' of a built-in function is used for
--
-- 1. computing the PLC type of the function to be used during type checking
-- 2. checking equality of the expected type of an argument of a builtin and the actual one
--    during evaluation, so that we can avoid unsafe-coercing
--
-- There exist two kinds of built-in functions:
--
-- 1. those whose denotation is known statically. E.g. the denotation of 'AddInteger' is @(+)@
-- 2. those whose denotation is computed at runtimefor. E.g. 'Trace' maps to a function whose
--    denotation is constructed in the 'IO' monad
--
-- Those functions that get their denotation at runtime make use of the @dyn@ parameter that
-- gets instantiated with a record containing interpretations for each of the "dynamic" built-in
-- functions. I.e. for each such function we simply extract its denotation from said record.
-- For "static" built-in function we ignore the @dyn@ record and construct the denotation
-- directly.
--
-- A costing function for a built-in function is computed from a cost model for all built-in
-- functions from a certain set, hence the @cost@ parameter.
data BuiltinMeaning term dyn cost =
    forall args res. BuiltinMeaning
        (TypeScheme term args res)
        (dyn -> FoldArgs args res)
        (cost -> FoldArgsEx args)
-- I tried making it @(forall term. HasConstantIn uni term => TypeScheme term args res)@ instead of
-- @TypeScheme term args res@, but 'toDynamicBuiltinMeaning' has to talk about
-- @KnownPolytype binds term args res a@ (note the @term@), because instances of 'KnownMonotype'
-- are constrained with @KnownType term arg@ and @KnownType term res@, and so the earliest we can
-- generalize from @term@ to @UniOf term@ is in 'toBuiltinMeaning'.
-- Besides, for 'BuiltinRuntime' we want to have a concrete 'TypeScheme' anyway for performance
-- reasons (there isn't much point in caching a value of a type with a constraint as it becomes a
-- function at runtime anyway, due to constraints being compiled as dictionaries).

-- | A 'BuiltinRuntime' is an instantiated (via 'toBuiltinRuntime') 'BuiltinMeaning'.
-- It contains info that is used during evaluation:
--
-- 1. the 'TypeScheme' of a builtin
-- 2. the 'Arity'
-- 3. the denotation
-- 4. the costing function
data BuiltinRuntime term =
    forall args res. BuiltinRuntime
        (TypeScheme term args res)
        Arity
        (FoldArgs args res)
        (FoldArgsEx args)

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun term = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime term)
    }

-- | Instantiate a 'BuiltinMeaning' given denotations of dynamic built-in functions and
-- a cost model.
toBuiltinRuntime :: dyn -> cost -> BuiltinMeaning term dyn cost -> BuiltinRuntime term
toBuiltinRuntime dyn cost (BuiltinMeaning sch f exF) =
    BuiltinRuntime sch (getArity sch) (f dyn) (exF cost)

-- | A type class for \"each function from a set of built-in functions has a 'BuiltinMeaning'\".
class (Bounded fun, Enum fun, Ix fun) => ToBuiltinMeaning uni fun where
    -- | The @dyn@ part of 'BuiltinMeaning'.
    type DynamicPart uni fun

    -- | The @cost@ part of 'BuiltinMeaning'.
    type CostingPart uni fun

    -- | Get the 'BuiltinMeaning' of a built-in function.
    toBuiltinMeaning
        :: HasConstantIn uni term
        => fun -> BuiltinMeaning term (DynamicPart uni fun) (CostingPart uni fun)

-- | Get the type of a built-in function.
typeOfBuiltinFunction :: ToBuiltinMeaning uni fun => fun -> Type TyName uni ()
typeOfBuiltinFunction fun = case toBuiltinMeaning @_ @_ @(Term TyName Name _ _ ()) fun of
    BuiltinMeaning sch _ _ -> typeSchemeToType sch

-- | Calculate runtime info for all built-in functions given denotations of dynamic builtins
-- and a cost model.
toBuiltinsRuntime
    :: ( dyn ~ DynamicPart uni fun, cost ~ CostingPart uni fun
       , HasConstantIn uni term, ToBuiltinMeaning uni fun
       )
    => dyn -> cost -> BuiltinsRuntime fun term
toBuiltinsRuntime dyn cost =
    BuiltinsRuntime . tabulateArray $ toBuiltinRuntime dyn cost . toBuiltinMeaning

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err term) m, AsMachineError err fun term, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri

{- Note [Automatic derivation of type schemes]
We use two type classes for automatic derivation of type schemes: 'KnownMonotype' and
'KnownPolytype'. The terminology is due to https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#The_Hindley%E2%80%93Milner_type_system

'KnownMonotype' and 'KnownPolytype' are responsible for deriving monomorphic and polymorphic types,
respectively. 'KnownMonotype' turns every argument that the Haskell denotation of a builtin
receives into a 'TypeSchemeArrow'. We extract the arguments from the type of the Haskell denotation
using the 'GetArgs' type family. 'KnownPolytype' turns every bound variable into a 'TypeSchemeAll'.
We extract variables from the type of the Haskell denotation using the 'ToBinds' type family
(in particular, see the @ToBinds (TypeScheme term args res)@ type instances). Variables are
collected in the order that they appear in (i.e. just like in Haskell). For example, processing
a type signature like

    const
        :: ( a ~ Opaque term (TyVarRep ('TyNameRep "a" 0))
           , b ~ Opaque term (TyVarRep ('TyNameRep "b" 1))
           )
        => b -> a -> b

with 'ToBinds' results in the following list of bindings:

    '[ 'Some ('TyNameRep "b" 1), 'Some ('TyNameRep "a" 0) ]

Higher-kinded type variables are fully supported.

The implementation of the 'KnownMonotype' and 'KnownPolytype' classes are structured in an
inference-friendly manner:

1. we compute @args@ using a type family ('GetArgs') in order to dispatch on the list of
   arguments of a built-in function in a way that doesn't force us to introduce overlapping
   instances
2. the @a -> res@ dependency allows us not to compute @res@ using a type family like with @args@
3. the @args res -> a@ dependency allows us not to mention @a@ in the type of 'knownMonotype'

The end result is that the user only has to specify the type of the denotation of a built-in
function and the 'TypeScheme' of the built-in function will be derived automatically. And in the
monomorphic case no types need to be specified at all.
-}

type family GetArgs a :: [GHC.Type] where
    GetArgs (a -> b) = a ': GetArgs b
    GetArgs _        = '[]

-- | A class that allows us to derive a monotype for a builtin.
class KnownMonotype term args res a | args res -> a, a -> res where
    knownMonotype :: TypeScheme term args res

-- | Once we've run out of term-level arguments, we return a 'TypeSchemeResult'.
instance (res ~ res', KnownType term res) => KnownMonotype term '[] res res' where
    knownMonotype = TypeSchemeResult Proxy

-- | Every term-level argument becomes as 'TypeSchemeArrow'.
instance (KnownType term arg, KnownMonotype term args res a) =>
            KnownMonotype term (arg ': args) res (arg -> a) where
    knownMonotype = Proxy `TypeSchemeArrow` knownMonotype

-- | Delete all @x@s from a list.
type family Delete x xs :: [a] where
    Delete _ '[]       = '[]
    Delete x (x ': xs) = Delete x xs
    Delete x (y ': xs) = y ': Delete x xs

-- | Delete all elements appearing in the first list from the second one and concatenate the lists.
type family Merge xs ys :: [a] where
    Merge '[]       ys = ys
    Merge (x ': xs) ys = x ': Delete x (Merge xs ys)

-- | 'Transparent' is used to cancel 'Opaque'. We need this in cases like
--
--     TyAppRep (TyVarRep ('TyNameRep "f" 0)) (Transparent Integer)
--
-- because 'ToBinds' only handles PLC types and so if it's applied to just 'Integer', then it's
-- stuck. The additional 'Transparent' wrapper allows us to move from handling PLC types back to
-- handling Haskell ones.
--
-- Don't use 'Transparent' when there's no surrounding 'Opaque'. It's of no use in that case and
-- you can get weird behavior.
newtype Transparent a = Transparent
    { unTransparent :: a
    }

instance KnownTypeAst uni a => KnownTypeAst uni (Transparent a) where
    toTypeAst _ = toTypeAst $ Proxy @a

instance KnownType term a => KnownType term (Transparent a) where
    makeKnown = makeKnown . unTransparent
    readKnown = fmap Transparent . readKnown

-- | Collect all unique variables (a variable consists of a textual name, a unique and a kind)
-- in an @x@.
type family ToBinds (x :: a) :: [Some TyNameRep]

type instance ToBinds (TyVarRep var) = '[ 'Some var ]
type instance ToBinds (TyAppRep fun arg) = Merge (ToBinds fun) (ToBinds arg)
type instance ToBinds (TyForallRep var a) = Delete ('Some var) (ToBinds a)
type instance ToBinds (Transparent a) = TypeToBinds a

-- | A standalone Haskell type either stands for a PLC type (when it's an 'Opaque') or
-- it's an actual Haskell type, in which case it doesn't contain any PLC type variables.
type family TypeToBinds (a :: GHC.Type) :: [Some TyNameRep] where
    TypeToBinds (Opaque _ rep) = ToBinds rep
    TypeToBinds _              = '[]

type instance ToBinds (TypeScheme term '[]           res) = TypeToBinds res
type instance ToBinds (TypeScheme term (arg ': args) res) =
    Merge (TypeToBinds arg) (ToBinds (TypeScheme term args res))

-- | A class that allows us to derive a polytype for a builtin.
class KnownPolytype (binds :: [Some TyNameRep]) term args res a | args res -> a, a -> res where
    knownPolytype :: Proxy binds -> TypeScheme term args res

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype term args res a => KnownPolytype '[] term args res a where
    knownPolytype _ = knownMonotype

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds term args res a) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) term args res a where
    knownPolytype _ = TypeSchemeAll @name @uniq @kind Proxy $ \_ -> knownPolytype (Proxy @binds)

-- See Note [Automatic derivation of type schemes]
-- | Construct the meaning for a dynamic built-in function by automatically deriving its
-- 'TypeScheme', given
--
-- 1. a function that extracts the denotation of the builtin from the record with denotations
--    of dynamic builtins
-- 2. an uninstantiated costing function
toDynamicBuiltinMeaning
    :: forall a term dyn cost binds args res.
       ( args ~ GetArgs a, a ~ FoldArgs args res, binds ~ ToBinds (TypeScheme term args res)
       , KnownPolytype binds term args res a
       )
    => (dyn -> a) -> (cost -> FoldArgsEx args) -> BuiltinMeaning term dyn cost
toDynamicBuiltinMeaning = BuiltinMeaning (knownPolytype (Proxy @binds) :: TypeScheme term args res)

-- See Note [Automatic derivation of type schemes]
-- | Construct the meaning for a static built-in function by automatically deriving its
-- 'TypeScheme', given
--
-- 1. the denotation of the builtin
-- 2. an uninstantiated costing function
toStaticBuiltinMeaning
    :: forall a term dyn cost binds args res.
       ( args ~ GetArgs a, a ~ FoldArgs args res, binds ~ ToBinds (TypeScheme term args res)
       , KnownPolytype binds term args res a
       )
    => a -> (cost -> FoldArgsEx args) -> BuiltinMeaning term dyn cost
toStaticBuiltinMeaning = toDynamicBuiltinMeaning . const
