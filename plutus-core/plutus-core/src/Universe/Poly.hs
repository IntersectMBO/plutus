{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Universe.Poly
    ( TypeApp
    , HasUniApply (..)
    , asTypeApp
    , withDecodedTypeApp
    , asTypeFun
    , withDecodedTypeFun
    ) where

import           Universe.Core

import qualified Data.Kind          as GHC
import           Data.Type.Equality
import           Type.Reflection

data TypeApp (a :: k)

class HasUniApply (uni :: GHC.Type -> GHC.Type) where
    matchUniRunTypeApp
        :: uni a
        -> r
        -> (uni (TypeApp a) -> r)
        -> r
    matchUniApply
        :: uni tfa
        -> r
        -> (forall k f a. tfa ~ TypeApp (f a :: k) => uni (TypeApp f) -> uni a -> r)
        -> r

asTypeApp
    :: forall uni ta m r. (Typeable ta, MonadFail m)
    => uni ta
    -> (forall (a :: GHC.Type). (ta ~ TypeApp a, Typeable a) => m r)
    -> m r
asTypeApp _ k = do
    App repT repA <- pure $ typeRep @ta
    let kindA = typeRepKind repA
        repT' = withTypeable kindA $ typeRep @TypeApp
    Just Refl <- pure $ repT `testEquality` repT'
    Just Refl <- pure $ typeRepKind repA `testEquality` typeRep @GHC.Type
    withTypeable repA k

withDecodedTypeApp
    :: forall uni r. Closed uni
    => (forall (a :: GHC.Type). Typeable a => uni (TypeApp a) -> DecodeUniM r)
    -> DecodeUniM r
withDecodedTypeApp k = withDecodedUni @uni $ \uniTA -> asTypeApp uniTA $ k uniTA

-- We only need this function, because GHC won't allow turning @repF@ into the @Typeable f@
-- constraint at the end of the definition for whatever stupid reason. So we do that in 'asTypeFun'.
withTypeFunRep
    :: forall proxy tf m r. (Typeable tf, MonadFail m)
    => proxy tf
    -> (forall k (f :: GHC.Type -> k). (tf ~ TypeApp f, Typeable k) => TypeRep f -> m r)
    -> m r
withTypeFunRep _ k = do
    App repT repF <- pure $ typeRep @tf
    let kindF = typeRepKind repF
    Fun repArg repRes <- pure kindF
    let repT' = withTypeable kindF $ typeRep @TypeApp
    Just Refl  <- pure $ repT `testEquality` repT'
    Just HRefl <- pure $ repArg `eqTypeRep` typeRep @GHC.Type
    Just Refl  <- pure $ typeRepKind repRes `testEquality` typeRep @GHC.Type
    withTypeable repRes $ k repF

asTypeFun
    :: forall proxy tf m r. (Typeable tf, MonadFail m)
    => proxy tf
    -> (forall k (f :: GHC.Type -> k). (tf ~ TypeApp f, Typeable k, Typeable f) => m r)
    -> m r
asTypeFun uniF k = withTypeFunRep uniF $ \repF -> withTypeable repF k

withDecodedTypeFun
    :: forall uni r. Closed uni
    => (forall k (f :: GHC.Type -> k). (Typeable k, Typeable f) => uni (TypeApp f) -> DecodeUniM r)
    -> DecodeUniM r
withDecodedTypeFun k = withDecodedUni @uni $ \uniF -> asTypeFun uniF $ k uniF
