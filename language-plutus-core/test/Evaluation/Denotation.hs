{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Evaluation.Denotation where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Data.GADT.Compare
import           Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

data Denotation object size r = forall a. Denotation
    { _denotationObject :: object
    , _denotationToTerm :: object -> Term TyName Name ()
    , _denotationItself :: a                              -- ^ The denotation of 'object'.
                                                          -- E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme size a r
    }

newtype Context head size = Context
    { unContext :: DMap (TypedBuiltin ()) (Denotation head size)
    }

denoteTypedBuiltinName :: TypedBuiltinName a r -> a -> Denotation BuiltinName size r
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (Constant () . BuiltinName ()) meta scheme

-- We should have this:
class IEq f where
    ieq :: f a -> f b -> Maybe (a :~: b)

-- 'Ord' is too much of course.
instance Ord size => GEq (TypedBuiltin size) where
    geq = geqDefault

geqDefault :: GCompare f => f a -> f b -> Maybe (a :~: b)
geqDefault a b | GEQ <- a `gcompare` b = Just Refl
geqDefault _ _ = Nothing

liftOrdering :: Ordering -> GOrdering a a
liftOrdering LT = GLT
liftOrdering EQ = GEQ
liftOrdering GT = GGT

instance Ord size => GCompare (TypedBuiltin size) where
    gcompare (TypedBuiltinSized size1 tbs1) (TypedBuiltinSized size2 tbs2) =
        case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , TypedBuiltinSizedInt ) -> mono
            (TypedBuiltinSizedBS  , TypedBuiltinSizedBS  ) -> mono
            (TypedBuiltinSizedSize, TypedBuiltinSizedSize) -> mono

            (TypedBuiltinSizedInt , _                    ) -> GLT
            (TypedBuiltinSizedBS  , TypedBuiltinSizedInt ) -> GGT
            (TypedBuiltinSizedBS  , _                    ) -> GLT
            (TypedBuiltinSizedSize, _                    ) -> GGT
        where
            mono :: GOrdering a a
            mono = liftOrdering $ size1 `compare` size2
    gcompare TypedBuiltinBool               TypedBuiltinBool               = GEQ

    gcompare (TypedBuiltinSized _ _)        TypedBuiltinBool               = GLT
    gcompare TypedBuiltinBool               (TypedBuiltinSized _ _)        = GGT

insertTypedBuiltinName
    :: TypedBuiltinName a r
    -> a
    -> Context BuiltinName size
    -> Context BuiltinName size
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta (Context vs) = Context $
    DMap.insert
        (typeSchemeResult scheme)
        (denoteTypedBuiltinName tbn meta)
        vs

typedBuiltinNames :: Context BuiltinName size
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger (+)
    $ Context DMap.empty
