-- | The universe used by default and its instances.

{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Default.Universe
    ( DefaultUni (..)
    , pattern DefaultUniList
    , pattern DefaultUniPair
    , pattern DefaultUniString
    , module Export  -- Re-exporting universes infrastructure for convenience.
    ) where

import           PlutusCore.Core
import           PlutusCore.Parsable

import           Control.Applicative
import qualified Data.ByteString     as BS
import           Data.Foldable
import qualified Data.Text           as Text
import           Universe            as Export

{- Note [PLC types and universes]
We encode built-in types in PLC as tags for Haskell types (the latter are also called meta-types),
see Note [Universes]. A built-in type in PLC is an inhabitant of

    Some (TypeIn uni)

where @uni@ is some universe, i.e. a collection of tags that have meta-types associated with them.

A value of a built-in type is a regular Haskell value stored in

    Some (ValueOf uni)

(together with the tag associated with its type) and such a value is also called a meta-constant.

The default universe has the following constructor (pattern synonym actually):

    DefaultUniList :: !(DefaultUni a) -> DefaultUni [a]

But note that this doesn't directly lead to interop between Plutus Core and Haskell, i.e. you can't
have a meta-list whose elements are of a PLC type. You can only have a meta-list constant with
elements of a meta-type (i.e. a type from the universe).

However it is possible to apply a built-in type to an arbitrary PLC/PIR type, since we can embed
a type of an arbitrary kind into 'Type' and then apply it via 'TyApp'. But we only use it to
get polymorphic built-in functions over polymorphic built-in types, since it's not possible
to juggle values of polymorphic built-in types instantiated with non-built-in types at runtime
(it's not even possible to represent such a value in the AST, even though it's possible to represent
such a 'Type').

Finally, it is not necessarily the case that we need to allow embedding PLC terms into meta-constants.
We already allow built-in names with polymorphic types. There might be a way to utilize this feature
and have meta-constructors as builtin names.
-}

-- See Note [Representing polymorphism].
-- | The universe used by default.
data DefaultUni a where
    DefaultUniInteger    :: DefaultUni (T Integer)
    DefaultUniByteString :: DefaultUni (T BS.ByteString)
    DefaultUniChar       :: DefaultUni (T Char)
    DefaultUniUnit       :: DefaultUni (T ())
    DefaultUniBool       :: DefaultUni (T Bool)
    DefaultUniProtoList  :: DefaultUni (T [])
    DefaultUniProtoPair  :: DefaultUni (T (,))
    DefaultUniApply      :: !(DefaultUni (T f)) -> !(DefaultUni (T a)) -> DefaultUni (T (f a))

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
    DefaultUniProtoList `DefaultUniApply` uniA
pattern DefaultUniPair uniA uniB =
    DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB
-- Just for backwards compatibility, probably should be removed at some point.
pattern DefaultUniString = DefaultUniList DefaultUniChar

deriveGEq ''DefaultUni

-- | For pleasing the coverage checker.
noMoreTypeFunctions :: DefaultUni (T (f :: a -> b -> c -> d)) -> any
noMoreTypeFunctions (f `DefaultUniApply` _) = noMoreTypeFunctions f

instance ToKind DefaultUni where
    toKind DefaultUniInteger        = kindOf DefaultUniInteger
    toKind DefaultUniByteString     = kindOf DefaultUniByteString
    toKind DefaultUniChar           = kindOf DefaultUniChar
    toKind DefaultUniUnit           = kindOf DefaultUniUnit
    toKind DefaultUniBool           = kindOf DefaultUniBool
    toKind DefaultUniProtoList      = kindOf DefaultUniProtoList
    toKind DefaultUniProtoPair      = kindOf DefaultUniProtoPair
    toKind (DefaultUniApply uniF _) = case toKind uniF of
        -- We can using @error@ here by having more type astronautics with 'Typeable',
        -- but having @error@ should be fine.
        Type _            -> error "Panic: a type function can't be of type *"
        KindArrow _ _ cod -> cod

instance HasUniApply DefaultUni where
    matchUniApply (DefaultUniApply f a) _ h = h f a
    matchUniApply _                     z _ = z

instance GShow DefaultUni where gshowsPrec = showsPrec
instance Show (DefaultUni a) where
    show DefaultUniInteger             = "integer"
    show DefaultUniByteString          = "bytestring"
    show DefaultUniChar                = "char"
    show DefaultUniUnit                = "unit"
    show DefaultUniBool                = "bool"
    show DefaultUniProtoList           = "list"
    show DefaultUniProtoPair           = "pair"
    show (uniF `DefaultUniApply` uniB) = case uniF of
        DefaultUniProtoList -> case uniB of
            DefaultUniChar -> "string"
            _              -> concat ["list (", show uniB, ")"]
        DefaultUniProtoPair -> concat ["pair (", show uniB, ")"]
        DefaultUniProtoPair `DefaultUniApply` uniA -> concat ["pair (", show uniA, ") (", show uniB, ")"]
        uniG `DefaultUniApply` _ `DefaultUniApply` _ -> noMoreTypeFunctions uniG

-- See Note [Parsing horribly broken].
instance Parsable (SomeTypeIn (Kinded DefaultUni)) where
    parse "bool"       = Just . SomeTypeIn $ Kinded DefaultUniBool
    parse "bytestring" = Just . SomeTypeIn $ Kinded DefaultUniByteString
    parse "char"       = Just . SomeTypeIn $ Kinded DefaultUniChar
    parse "integer"    = Just . SomeTypeIn $ Kinded DefaultUniInteger
    parse "unit"       = Just . SomeTypeIn $ Kinded DefaultUniUnit
    parse "string"     = Just . SomeTypeIn $ Kinded DefaultUniString
    parse text         = asum
        [ do
            aT <- Text.stripPrefix "[" text >>= Text.stripSuffix "]"
            SomeTypeIn (Kinded a) <- parse aT
            Refl <- checkStar @DefaultUni a
            Just . SomeTypeIn . Kinded $ DefaultUniList a
        , do
            abT <- Text.stripPrefix "(" text >>= Text.stripSuffix ")"
            -- Note that we don't allow whitespace after @,@ (but we could).
            -- Anyway, looking for a single comma is just plain wrong, as we may have a nested
            -- tuple (and it can be left- or right- or both-nested), so we're running into
            -- the same parsing problem as with constants.
            case Text.splitOn "," abT of
                [aT, bT] -> do
                    SomeTypeIn (Kinded a) <- parse aT
                    Refl <- checkStar @DefaultUni a
                    SomeTypeIn (Kinded b) <- parse bT
                    Refl <- checkStar @DefaultUni b
                    Just . SomeTypeIn . Kinded $ DefaultUniPair a b
                _ -> Nothing
        ]

instance DefaultUni `Contains` Integer       where knownUni = DefaultUniInteger
instance DefaultUni `Contains` BS.ByteString where knownUni = DefaultUniByteString
instance DefaultUni `Contains` Char          where knownUni = DefaultUniChar
instance DefaultUni `Contains` ()            where knownUni = DefaultUniUnit
instance DefaultUni `Contains` Bool          where knownUni = DefaultUniBool
instance DefaultUni `Contains` []            where knownUni = DefaultUniProtoList
instance DefaultUni `Contains` (,)           where knownUni = DefaultUniProtoPair

instance (DefaultUni `Contains` f, DefaultUni `Contains` a) => DefaultUni `Contains` f a where
    knownUni = knownUni `DefaultUniApply` knownUni

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of PLC]
-}

instance Closed DefaultUni where
    type DefaultUni `Everywhere` constr =
        ( constr `Permits` Integer
        , constr `Permits` BS.ByteString
        , constr `Permits` Char
        , constr `Permits` ()
        , constr `Permits` Bool
        , constr `Permits` []
        , constr `Permits` (,)
        )

    -- See Note [Stable encoding of tags].
    encodeUni DefaultUniInteger           = [0]
    encodeUni DefaultUniByteString        = [1]
    encodeUni DefaultUniChar              = [2]
    encodeUni DefaultUniUnit              = [3]
    encodeUni DefaultUniBool              = [4]
    encodeUni DefaultUniProtoList         = [5]
    encodeUni DefaultUniProtoPair         = [6]
    encodeUni (DefaultUniApply uniF uniA) = 7 : encodeUni uniF ++ encodeUni uniA

    -- See Note [Decoding universes].
    -- See Note [Stable encoding of tags].
    withDecodedUni k = peelUniTag >>= \case
        0 -> k DefaultUniInteger
        1 -> k DefaultUniByteString
        2 -> k DefaultUniChar
        3 -> k DefaultUniUnit
        4 -> k DefaultUniBool
        5 -> k DefaultUniProtoList
        6 -> k DefaultUniProtoPair
        7 ->
            withDecodedUni @DefaultUni $ \uniF ->
                withDecodedUni @DefaultUni $ \uniA ->
                    withApplicable uniF uniA $
                        k $ uniF `DefaultUniApply` uniA
        _ -> empty

    bring
        :: forall constr a r proxy. DefaultUni `Everywhere` constr
        => proxy constr -> DefaultUni (T a) -> (constr a => r) -> r
    bring _ DefaultUniInteger    r = r
    bring _ DefaultUniByteString r = r
    bring _ DefaultUniChar       r = r
    bring _ DefaultUniUnit       r = r
    bring _ DefaultUniBool       r = r
    bring p (DefaultUniProtoList `DefaultUniApply` uniA) r =
        bring p uniA r
    bring p (DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB) r =
        bring p uniA $ bring p uniB r
    bring _ (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
        noMoreTypeFunctions f
