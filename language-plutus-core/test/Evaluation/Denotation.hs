{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Evaluation.Denotation where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Data.Semigroup
import           Data.Functor.Compose
import           Control.Monad
import qualified Data.ByteString.Lazy as BSL
import           Data.GADT.Compare
import           Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

-- | Haskell denotation of a PLC object. An object can be a 'BuiltinName' or a variable for example.
data Denotation object size r = forall a. Denotation
    { _denotationObject :: object                         -- ^ A PLC object.
    , _denotationToTerm :: object -> Term TyName Name ()  -- ^ How to embed the object into a term.
    , _denotationItself :: a                              -- ^ The denotation of the object.
                                                          -- E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme size a r            -- ^ The 'TypeScheme' of the object.
                                                          -- See 'sizeIntIntInt' for example.
    }

data MemberDenotation r = forall object. MemberDenotation (Denotation object Size r)

newtype Context = Context
    { unContext :: DMap (TypedBuiltin ()) (Compose [] MemberDenotation)
    }

-- Here the only search that we need to perform is the search for things that return an appropriate @r@,
-- be them variables or functions. Better if we also take types of arguments into account, but it is
-- not required as we can always generate an argument out of thin air in a rank-0 setting (without @Void@).

-- This should allow us to generate terms like (likely less sensible, but still well-typed)

-- (\(f : (integer -> bytestring) -> bool) -> f $ \i -> intToByteString i)
--     (\g -> g 3 `equalsByteString` intToByteString 3)

-- which is a pretty good start.

denoteTypedBuiltinName :: TypedBuiltinName a r -> a -> Denotation BuiltinName size r
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (Constant () . BuiltinName ()) meta scheme

liftOrdering :: Ordering -> GOrdering a a
liftOrdering LT = GLT
liftOrdering EQ = GEQ
liftOrdering GT = GGT

-- I tried using the 'dependent-sum-template' package,
-- but see https://stackoverflow.com/q/50048842/3237465
-- I tried to abstract the pattern of @case (tbs1, tbs2) of@
-- without a performance penalty, but it's not that straightforward.
-- I do not want to spend any more time on this, so here are dumb and straightforward instances.
instance Eq size => GEq (TypedBuiltin size) where
    geq (TypedBuiltinSized size1 tbs1) (TypedBuiltinSized size2 tbs2) = do
        guard $ size1 == size2
        case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , TypedBuiltinSizedInt ) -> Just Refl
            (TypedBuiltinSizedBS  , TypedBuiltinSizedBS  ) -> Just Refl
            (TypedBuiltinSizedSize, TypedBuiltinSizedSize) -> Just Refl
            (_                    , _                    ) -> Nothing
    geq TypedBuiltinBool               TypedBuiltinBool               = Just Refl
    geq _                              _                              = Nothing

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

{- -- This is rejected, because the 'Applicative' instance requires 'g' to be 'Applicative'.
-- Hence we can't simply use '(<|>)' in 'DMap.insertWith\'' below. Something is not right here.
instance Alternative f => Alternative (Compose f g) where
    empty = Compose empty
    Compose x <|> Compose y = Compose (x <|> y)
-}

insertTypedBuiltinName :: TypedBuiltinName a r -> a -> Context -> Context
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta (Context vs) = Context $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        (typeSchemeResult scheme)
        (Compose [MemberDenotation $ denoteTypedBuiltinName tbn meta])
        vs

typedBuiltinNames :: Context
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger           (+)
    . insertTypedBuiltinName typedSubtractInteger      (-)
    . insertTypedBuiltinName typedMultiplyInteger      (*)
    . insertTypedBuiltinName typedDivideInteger        div
    . insertTypedBuiltinName typedRemainderInteger     mod
    . insertTypedBuiltinName typedLessThanInteger      (<)
    . insertTypedBuiltinName typedLessThanEqInteger    (<=)
    . insertTypedBuiltinName typedGreaterThanInteger   (>)
    . insertTypedBuiltinName typedGreaterThanEqInteger (>=)
    . insertTypedBuiltinName typedEqInteger            (==)
    . insertTypedBuiltinName typedResizeInteger        (const id)
--     . insertTypedBuiltinName typedIntToByteString      undefined
    . insertTypedBuiltinName typedConcatenate          (<>)
    . insertTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
    . insertTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
--     . insertTypedBuiltinName typedSHA2                 undefined
--     . insertTypedBuiltinName typedSHA3                 undefined
--     . insertTypedBuiltinName typedVerifySignature      undefined
    . insertTypedBuiltinName typedResizeByteString     (const id)
    . insertTypedBuiltinName typedEqByteString         (==)
--     . insertTypedBuiltinName typedTxHash               undefined
    $ Context DMap.empty
