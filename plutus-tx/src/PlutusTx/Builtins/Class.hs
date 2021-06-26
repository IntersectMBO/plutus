{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.Class where

import           Data.Kind

import           Data.ByteString            (ByteString)
import           PlutusTx.Builtins.Internal

import           Data.String                (IsString (..))

import qualified GHC.Magic                  as Magic

import           Prelude                    hiding (fst, head, null, snd, tail)

type BuiltinRep :: Type -> Type
{-|
The builtin Plutus Core type which represents the given type.

For example, Plutus Core has builtin booleans, but the Haskell 'Bool' type can also be
compiled into Plutus Core as a datatype. The 'FromBuiltin' and 'ToBuiltin' instances allows us to
convert between those in on-chain code.
-}
type family BuiltinRep a

{-|
A class witnessing the ability to convert from the builtin representation to the Haskell representation.
-}
class FromBuiltin a where
    fromBuiltin :: BuiltinRep a -> a

{-|
A class witnessing the ability to convert from the Haskell representation to the builtin representation.
-}
class ToBuiltin a where
    toBuiltin :: a -> BuiltinRep a

type instance BuiltinRep Integer = BuiltinInteger
instance FromBuiltin Integer where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin Integer where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

type instance BuiltinRep Bool = BuiltinBool
instance FromBuiltin Bool where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin b = ifThenElse b True False
instance ToBuiltin Bool where
    {-# INLINABLE toBuiltin #-}
    toBuiltin b = if b then true else false

type instance BuiltinRep () = BuiltinUnit

{- Note [Strict conversions to/from unit]
Converting to/from unit *should* be straightforward: just ``const ()`.`
*But* GHC is very good at optimizing this, and we sometimes use unit
where side effects matter, e.g. as the result of `trace`. So GHC will
tend to turn `fromBuiltin (trace s)` into `()`, which is wrong.

So we want our conversions to/from unit to be strict in Haskell. This
means we need to case pointlessly on the argument, which means we need
case on unit (`chooseUnit`) as a builtin. But then it all works okay.
-}

instance FromBuiltin () where
    -- See Note [Strict conversions to/from unit]
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin u = chooseUnit u ()
instance ToBuiltin () where
    -- See Note [Strict conversions to/from unit]
    {-# INLINABLE toBuiltin #-}
    toBuiltin x = case x of () -> unitval

type instance BuiltinRep ByteString = BuiltinByteString
instance FromBuiltin ByteString where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin ByteString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

type instance BuiltinRep Char = BuiltinChar
instance FromBuiltin Char where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin Char where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

{- Note [noinline hack]
For some functions we have two conflicting desires:
- We want to have the unfolding available for the plugin.
- We don't want the function to *actually* get inlined before the plugin runs, since we rely
on being able to see the original function for some reason.

'INLINABLE' achieves the first, but may cause the function to be inlined too soon.

We can solve this at specific call sites by using the 'noinline' magic function from
GHC. This stops GHC from inlining it. As a bonus, it also won't be inlined if
that function is compiled later into the body of another function.

We do therefore need to handle 'noinline' in the plugin, as it itself does not have
an unfolding.
-}

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinString'
    {-# INLINE fromString #-}
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinString

{-# INLINABLE stringToBuiltinString #-}
stringToBuiltinString :: String -> BuiltinString
stringToBuiltinString = go
    where
        go []     = emptyString
        go (x:xs) = charToString x `appendString` go xs

type instance BuiltinRep BuiltinString = BuiltinString
instance FromBuiltin BuiltinString where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin BuiltinString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

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

type instance BuiltinRep (a,b) = BuiltinPair (BuiltinRep a) (BuiltinRep b)
instance (FromBuiltin a, FromBuiltin b) => FromBuiltin (a,b) where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
instance ToBuiltin (BuiltinData, BuiltinData) where
    {-# INLINABLE toBuiltin #-}
    toBuiltin (d1, d2) = mkPairData d1 d2

type instance BuiltinRep [a] = BuiltinList (BuiltinRep a)
instance FromBuiltin a => FromBuiltin [a] where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = builtinListToList

{- Note [Specializing recursive FromBuiltin instances]
Recursive instances of `FromBuiltin`, such as the one for lists, are hard for the plugin to deal with.
They have a superclass constraint which contains functions in terms of an *unknown* type family application
(i.e. we have `fromBuiltin :: BuiltinRep a -> a`, where `BuiltinRep a` is unknown).
The plugin requires all type family applications to reduce away, so this is a no go.

However, this will work in a specific instance provided everything gets inlined and specialized away:
if we can see that the superclass instance is really a known instance, we can redue the `BuiltinRep`
application and everything is fine.

Unfortunately, this means we have to rely on GHC's specializer. This is tricky with the plugin: sometimes
specializations don't get unfoldings and things break, so we often turn off specialization. In this instance
we want to keep it on (primarily in PlutusTx.Builtins), and we jump through some hoops to makes sure
we have unfoldings for everything.

In particular, GHC *won't* include unfoldings for *recursive* specializations. So we hide the recursion in a
local helper function, which makes it all work out.

TROUBLESHOOTING: if this all stops working, another solution that worked was to make specialized versions
of `fromBuiltin` for the types that we need *in this module*. They then get optimized well here, and it
works out okay.
-}

-- See Note [Specializing recursive FromBuiltin instances]
{-# SPECIALIZE builtinListToList :: BuiltinList (BuiltinPair BuiltinData BuiltinData) -> [(BuiltinData, BuiltinData)] #-}
{-# SPECIALIZE builtinListToList :: BuiltinList BuiltinData -> [BuiltinData] #-}
builtinListToList :: forall a . (FromBuiltin a) => BuiltinList (BuiltinRep a) -> [a]
builtinListToList = go
  where
      -- The combination of both INLINABLE and a type signature seems to stop this getting lifted to the top
      -- level, which is what we want (we need it to be a local otherwise it doesn't get a proper unfolding)
      {-# INLINABLE go #-}
      go :: BuiltinList (BuiltinRep a) -> [a]
      -- Note that we are using builtin ifThenElse here so this is *strict* application! So we need to do
      -- the manual laziness ourselves. We could instead convert the boolean to a Haskell boolean and use
      -- normal if, but we might as well use the builtins directly here.
      go l = (ifThenElse (null l) (\_ -> []) (\_ -> fromBuiltin (head l):go (tail l))) unitval

instance ToBuiltin [BuiltinData] where
    {-# INLINABLE toBuiltin #-}
    toBuiltin []     = mkNilData unitval
    toBuiltin (d:ds) = mkConsData d (toBuiltin ds)

instance ToBuiltin [(BuiltinData, BuiltinData)] where
    {-# INLINABLE toBuiltin #-}
    toBuiltin []     = mkNilPairData unitval
    toBuiltin (d:ds) = mkConsPairData (toBuiltin d) (toBuiltin ds)

type instance BuiltinRep BuiltinData = BuiltinData
instance FromBuiltin BuiltinData where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin BuiltinData where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id
