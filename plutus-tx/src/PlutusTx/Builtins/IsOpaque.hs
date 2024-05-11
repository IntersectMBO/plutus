{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Builtins.IsOpaque where

import PlutusTx.Base (id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal

import Data.Kind qualified as GHC
import Data.String (IsString (..))
import Data.Text qualified as Text
import GHC.Magic qualified as Magic
import Prelude qualified as Haskell (String)

obfuscatedId :: a -> a
obfuscatedId a = a
{-# NOINLINE obfuscatedId #-}

stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
stringToBuiltinByteString str = encodeUtf8 $ stringToBuiltinString str
{-# INLINABLE stringToBuiltinByteString #-}

stringToBuiltinString :: Haskell.String -> BuiltinString
-- To explain why the obfuscatedId is here
-- See Note [noinline hack]
stringToBuiltinString str = obfuscatedId (BuiltinString $ Text.pack str)
{-# INLINABLE stringToBuiltinString #-}

{- Same noinline hack as with `String` type. -}
instance IsString BuiltinByteString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinByteString'
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinByteString
    {-# INLINE fromString #-}

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinString'
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinString
    {-# INLINE fromString #-}

type HasFromOpaque :: GHC.Type -> GHC.Type -> GHC.Constraint
class HasFromOpaque arep a | arep -> a where
    fromOpaque :: arep -> a
    default fromOpaque :: a ~ arep => arep -> a
    fromOpaque = id
    {-# INLINABLE fromOpaque #-}

type HasToOpaque :: GHC.Type -> GHC.Type -> GHC.Constraint
class HasToOpaque a arep | a -> arep where
    toOpaque :: a -> arep
    default toOpaque :: a ~ arep => a -> arep
    toOpaque = id
    {-# INLINABLE toOpaque #-}

instance HasFromOpaque BuiltinInteger BuiltinInteger
instance HasToOpaque BuiltinInteger BuiltinInteger

instance HasFromOpaque BuiltinByteString BuiltinByteString
instance HasToOpaque BuiltinByteString BuiltinByteString

instance HasFromOpaque BuiltinString BuiltinString
instance HasToOpaque BuiltinString BuiltinString

instance HasFromOpaque BuiltinUnit () where
    fromOpaque u = chooseUnit u ()
    {-# INLINABLE fromOpaque #-}
instance HasToOpaque () BuiltinUnit where
    toOpaque x = case x of () -> unitval
    {-# INLINABLE toOpaque #-}

instance HasFromOpaque BuiltinBool Bool where
    fromOpaque b = ifThenElse b True False
    {-# INLINABLE fromOpaque #-}
instance HasToOpaque Bool BuiltinBool where
    toOpaque b = if b then true else false
    {-# INLINABLE toOpaque #-}

instance HasFromOpaque arep a => HasFromOpaque (BuiltinList arep) [a] where
    fromOpaque = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting
          -- lifted to the top level, which means it gets a proper unfolding, which means that
          -- specialization can work, which can actually help quite a bit here.
          go :: BuiltinList arep -> [a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we
          -- need to do the manual laziness ourselves.
          go l = chooseList l (\_ -> []) (\_ -> fromOpaque (head l) : go (tail l)) unitval
          {-# INLINABLE go #-}
    {-# INLINABLE fromOpaque #-}
instance HasToOpaque [BuiltinData] (BuiltinList BuiltinData) where
    toOpaque = goList where
        goList :: [BuiltinData] -> BuiltinList BuiltinData
        goList []     = mkNilData unitval
        goList (d:ds) = mkCons (toOpaque d) (goList ds)
    {-# INLINE toOpaque #-}
instance
        HasToOpaque
            [(BuiltinData, BuiltinData)]
            (BuiltinList (BuiltinPair BuiltinData BuiltinData)) where
    toOpaque = goList where
        goList :: [(BuiltinData, BuiltinData)] -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
        goList []     = mkNilPairData unitval
        goList (d:ds) = mkCons (toOpaque d) (goList ds)
    {-# INLINE toOpaque #-}

instance (HasFromOpaque arep a, HasFromOpaque brep b) =>
        HasFromOpaque (BuiltinPair arep brep) (a, b) where
    fromOpaque p = (fromOpaque $ fst p, fromOpaque $ snd p)
    {-# INLINABLE fromOpaque #-}
instance HasToOpaque (BuiltinData, BuiltinData) (BuiltinPair BuiltinData BuiltinData) where
    toOpaque (d1, d2) = mkPairData (toOpaque d1) (toOpaque d2)
    {-# INLINABLE toOpaque #-}

instance HasFromOpaque BuiltinData BuiltinData
instance HasToOpaque BuiltinData BuiltinData

instance HasFromOpaque BuiltinBLS12_381_G1_Element BuiltinBLS12_381_G1_Element
instance HasToOpaque BuiltinBLS12_381_G1_Element BuiltinBLS12_381_G1_Element

instance HasFromOpaque BuiltinBLS12_381_G2_Element BuiltinBLS12_381_G2_Element
instance HasToOpaque BuiltinBLS12_381_G2_Element BuiltinBLS12_381_G2_Element

instance HasFromOpaque BuiltinBLS12_381_MlResult BuiltinBLS12_381_MlResult
instance HasToOpaque BuiltinBLS12_381_MlResult BuiltinBLS12_381_MlResult

-- TODO: FIX THE NOTES

{- Note [Builtin types and their Haskell versions]
Consider the builtin pair type. In Plutus Tx, we have an (opaque) type for
this. It's opaque because you can't actually pattern match on it, instead you can
only in fact use the specific functions that are available as builtins.

We _also_ have the normal Haskell pair type. This is very different: you can
pattern match on it, and you can use whatever user-defined functions you like on it.

Users would really like to use the latter, and not the former. So we often want
to _wrap_ our builtin functions with little adapters that convert between the
"opaque builtin" "version" of a type and the "normal Haskell" "version" of a type.

This is what the ToBuiltin and FromBuiltin classes do. They let us write wrappers
for builtins relatively consistently by just calling toBuiltin on their arguments
and fromBuiltin on the result. They shouldn't really be used otherwise.

Ideally, we would not have instances for types which don't have a different
Haskell representation type, such as Integer. Integer in Plutus Tx user code _is_ the
opaque builtin type, we don't expose a different one. So there's no conversion to
do. However, this interacts badly with the instances for polymorphic builtin types, which
also convert the type _inside_ them. (This is necessary to avoid doing multiple
traversals of the type, e.g. we don't want to turn a builtin list into a Haskell
list, and then traverse it again to conver the contents). Then we _need_ instances
for all builtin types, even if they don't quite make sense.

Possibly this indicates that these type classes are a bit too 'ad-hoc' and we should
get rid of them.
-}

{- Note [From/ToBuiltin instances for polymorphic builtin types]
For various technical reasons
(see Note [Representable built-in functions over polymorphic built-in types])
it's not always easy to provide polymorphic constructors for builtin types, but
we can usually provide destructors.

What this means in practice is that we can write a generic FromBuiltin instance
for pairs that makes use of polymorphic fst/snd builtins, but we can't write
a polymorphic ToBuiltin instance because we'd need a polymorphic version of (,).

Instead we write monomorphic instances corresponding to monomorphic constructor
builtins that we add for specific purposes.
-}

{- Note [Fundeps versus type families in To/FromBuiltin]
We could use a type family here to get the builtin representation of a type. After all, it's
entirely determined by the Haskell type.

However, this is harder for the plugin to deal with. It's okay to have a type variable
for the representation type that needs to be instantiated later, but it's *not* okay to
have an irreducible type application on a type variable. So fundeps are much nicer here.
-}

{- Note [Strict conversions to/from unit]
Converting to/from unit *should* be straightforward: just `const ()`.
*But* GHC is very good at optimizing this, and we sometimes use unit
where side effects matter, e.g. as the result of `trace`. So GHC will
tend to turn `fromBuiltin (trace s)` into `()`, which is wrong.

So we want our conversions to/from unit to be strict in Haskell. This
means we need to case pointlessly on the argument, which means we need
case on unit (`chooseUnit`) as a builtin. But then it all works okay.
-}
