{-# LANGUAGE ConstraintKinds          #-}
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

-- | This module implements custom pretty printing of PIR terms, used for dumping
-- compilation runs that can be parsed by the Rocq PIR certifier. The targeted
-- syntax is very similar to that of derived Show instances, but differs in a few places:
--
--   * No record syntax (this cannot be parsed in Rocq)
--   * String and ByteString literals are printed as byte sequences (literals are treated
--     differently in Rocq)
--
-- In all other cases, existing instances of Show are reused.
--
-- This works by instantiating some type parameters differently for terms:
--
--    Term (AsRocq name) (AsRocq tyname) (AsRocqUni uni) fun
--
-- Here `AsRocq` and `AsRocqUni` are newtype wrappers that allow defining additional Show instances

module PlutusIR.Core.Instance.ShowRocq where

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusIR.Core.Type

import Data.ByteString (ByteString, unpack)
import Data.Kind (Constraint)
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Data.Vector.Strict (Vector, toList)
import Data.Word (Word8)
import Text.Printf

type ComposeC :: forall a b. (b -> Constraint) -> (a -> b) -> a -> Constraint
class c (f x) => ComposeC c f x
instance c (f x) => ComposeC c f x

type AsRocqK :: forall k. k -> k
data family AsRocqK a

type AsRocq = AsRocqK @GHC.Type
newtype instance AsRocqK a = AsRocq a

showAsRocq :: Show (AsRocq a) => a -> String
showAsRocq = show . AsRocq

type AsRocqUni :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
data AsRocqUni uni a where
    AsRocqUni :: uni (Esc a) -> AsRocqUni uni (Esc (AsRocqK a))

-- | Groups all constraints needed for fully polymorphic Terms
type ShowRocq tyname name uni fun a =
  ( Show (AsRocq tyname)
  , Show (AsRocq name)
  , Show fun
  , Everywhere uni (ComposeC Show AsRocq)
  , GShow (AsRocqUni uni)
  )

-- | Groups all constraints needed for PIR terms (with instantiated names)
type ShowRocqNamed uni fun a =
  ( Show fun
  , Everywhere uni (ComposeC Show AsRocq)
  , GShow (AsRocqUni uni)
  )

-- * Instances for type universes

instance Closed uni => Closed (AsRocqUni uni) where
    type AsRocqUni uni `Everywhere` constr = uni `Everywhere` ComposeC constr AsRocq

    bring
        :: forall constr a r proxy. uni `Everywhere` ComposeC constr AsRocq
        => proxy constr -> AsRocqUni uni (Esc a) -> (constr a => r) -> r
    bring _ (AsRocqUni uni) r = bring (Proxy @(ComposeC constr AsRocq)) uni r

    encodeUni (AsRocqUni uni) = encodeUni uni

    withDecodedUni k = withDecodedUni $ \uni -> k (AsRocqUni uni)

instance GShow (AsRocqUni DefaultUni) where
    gshowsPrec pr (AsRocqUni a) = showsPrec pr a

deriving newtype instance Show (AsRocq Integer)
deriving newtype instance Show (AsRocq ())
deriving newtype instance Show (AsRocq Bool)
deriving via [AsRocq a] instance Show (AsRocq a) => Show (AsRocq [a])
deriving via (AsRocq a, AsRocq b) instance (Show (AsRocq a), Show (AsRocq b))
  => Show (AsRocq (a, b))
deriving newtype instance Show (AsRocq Data)
deriving newtype instance Show (AsRocq BLS12_381.G1.Element)
deriving newtype instance Show (AsRocq BLS12_381.G2.Element)
deriving newtype instance Show (AsRocq BLS12_381.Pairing.MlResult)


instance Show (AsRocq a) => Show (AsRocq (Vector a)) where
    showsPrec p (AsRocq v) = showsPrec p (map AsRocq (toList v))
instance Show (AsRocq Text) where
    showsPrec p (AsRocq text) = showsPrec p (map AsRocq (unpack $ Text.encodeUtf8 text))
instance Show (AsRocq Word8) where
    -- Matches constructor notation of Coq.Init.Byte
    show (AsRocq w) = printf "x%02x" w
instance Show (AsRocq ByteString) where
    showsPrec p (AsRocq bs) = showsPrec p (map AsRocq (unpack bs))

-- * Names
-- These instances mimic GHC derived show instances, if they were defined without record syntax.

instance Show (AsRocq Name) where
  showsPrec p (AsRocq (Name x y)) =
    showParen (p >= 11) $
      showString "Name" .
      showString " " .
      showsPrec 11 (AsRocq x) .
      showString " " .
      showsPrec 11 (AsRocq y)

instance Show (AsRocq TyName) where
  showsPrec p (AsRocq (TyName x)) =
    showParen (p >= 11) $
      showString "TyName" .
      showString " " .
      showsPrec 11 (AsRocq x)

instance Show (AsRocq Unique) where
  showsPrec p (AsRocq (Unique n)) =
    showParen (p >= 11) $
      showString "Unique" .
      showString " " .
      showsPrec 11 n

instance
  ( Show (AsRocq tyname)
  , Show (AsRocq name)
  , GShow (AsRocqUni uni)
  , Closed uni, AsRocqUni uni `Everywhere` Show
  , Show fun
  , Show ann
  ) => Show (AsRocq (Term tyname name uni fun ann)) where
    showsPrec pr (AsRocq term) =
      showsPrec pr .
      mapName AsRocq .
      mapTyName AsRocq .
      mapUni fTy fConst $
        term
      where
        fConst (Some (ValueOf uni x)) = Some (ValueOf (AsRocqUni uni) (AsRocq x))
        fTy (SomeTypeIn ty) = SomeTypeIn (AsRocqUni ty)


