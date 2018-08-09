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

data Denotation object size r = forall a. Denotation
    { _denotationObject :: object
    , _denotationToTerm :: object -> Term TyName Name ()
    , _denotationItself :: a                              -- ^ The denotation of 'object'.
                                                          -- E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme size a r
    }

newtype Context head size = Context
    { unContext :: DMap (TypedBuiltin ()) (Compose [] (Denotation head size))
    }

denoteTypedBuiltinName :: TypedBuiltinName a r -> a -> Denotation BuiltinName size r
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (Constant () . BuiltinName ()) meta scheme

liftOrdering :: Ordering -> GOrdering a a
liftOrdering LT = GLT
liftOrdering EQ = GEQ
liftOrdering GT = GGT

-- I tried using the 'dependent-sum-template' package,
-- but see https://stackoverflow.com/q/50048842/3237465
-- I do not want to spend any more time on this, so
-- here are dumb and straightforward instances.
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

insertTypedBuiltinName
    :: TypedBuiltinName a r
    -> a
    -> Context BuiltinName size
    -> Context BuiltinName size
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta (Context vs) = Context $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        (typeSchemeResult scheme)
        (Compose [denoteTypedBuiltinName tbn meta])
        vs

typedBuiltinNames :: Context BuiltinName size
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
