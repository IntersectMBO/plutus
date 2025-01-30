{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE UndecidableSuperClasses  #-}

module UntypedPlutusCore.Core.Instance.CoqShow where

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Default.Universe
import UntypedPlutusCore.Core.Type

import Data.ByteString (ByteString)
import Data.Kind (Constraint)
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text

type ComposeC :: forall a b. (b -> Constraint) -> (a -> b) -> a -> Constraint
class c (f x) => ComposeC c f x
instance c (f x) => ComposeC c f x

type AsCoqK :: forall k. k -> k
data family AsCoqK a

type AsCoq = AsCoqK @GHC.Type
newtype instance AsCoqK a = AsCoq a

showAsCoq :: Show (AsCoq a) => a -> String
showAsCoq = show . AsCoq

type AsCoqUni :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
data AsCoqUni uni a where
    AsCoqUni :: uni (Esc a) -> AsCoqUni uni (Esc (AsCoqK a))

instance Closed uni => Closed (AsCoqUni uni) where
    type AsCoqUni uni `Everywhere` constr = uni `Everywhere` ComposeC constr AsCoq

    bring
        :: forall constr a r proxy. uni `Everywhere` ComposeC constr AsCoq
        => proxy constr -> AsCoqUni uni (Esc a) -> (constr a => r) -> r
    bring _ (AsCoqUni uni) r = bring (Proxy @(ComposeC constr AsCoq)) uni r

    encodeUni (AsCoqUni uni) = encodeUni uni

    withDecodedUni k = withDecodedUni $ \uni -> k (AsCoqUni uni)

instance
        ( Show name
        , GShow (AsCoqUni uni)
        , Closed uni, AsCoqUni uni `Everywhere` Show
        , Show fun
        , Show ann
        ) => Show (AsCoq (Term name uni fun ann)) where
    showsPrec pr (AsCoq term) = showsPrec pr $ mapUni f term where
        f (Some (ValueOf uni x)) = Some (ValueOf (AsCoqUni uni) (AsCoq x))

instance GShow (AsCoqUni DefaultUni) where
    gshowsPrec pr (AsCoqUni a) = showsPrec pr a

deriving newtype instance Show (AsCoq Integer)
deriving newtype instance Show (AsCoq ByteString)
deriving newtype instance Show (AsCoq ())
deriving newtype instance Show (AsCoq Bool)
deriving via [AsCoq a] instance Show (AsCoq a) => Show (AsCoq [a])
deriving via (AsCoq a, AsCoq b) instance (Show (AsCoq a), Show (AsCoq b)) => Show (AsCoq (a, b))
deriving newtype instance Show (AsCoq Data)
deriving newtype instance Show (AsCoq BLS12_381.G1.Element)
deriving newtype instance Show (AsCoq BLS12_381.G2.Element)
deriving newtype instance Show (AsCoq BLS12_381.Pairing.MlResult)
instance Show (AsCoq Text) where
    show (AsCoq text) = Text.unpack text
