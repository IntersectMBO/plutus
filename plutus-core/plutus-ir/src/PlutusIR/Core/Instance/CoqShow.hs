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
--   * No record syntax (this cannot be parsed in Coq)
--   * String and ByteString literals are printed as byte sequences (literals are treated
--     differently in Rocq)
--
-- In all other cases, existing instances of Show are reused.
--
-- This works by instantiating some type parameters differently for terms:
--
--    Term (AsCoq name) (AsCoq tyname) (AsCoqUni uni) fun
--
-- Here `AsCoq` and `AsCoqUni` are newtype wrappers that allow defining additional Show instances

module PlutusIR.Core.Instance.CoqShow where

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
import Data.Word (Word8)
import Text.Printf

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

-- | Groups all constraints needed for fully polymorphic Terms
type CoqShow tyname name uni fun a =
  ( Show (AsCoq tyname)
  , Show (AsCoq name)
  , Show fun
  , Everywhere uni (ComposeC Show AsCoq)
  , GShow (AsCoqUni uni)
  )

-- | Groups all constraints needed for PIR terms (with instantiated names)
type CoqShowNamed uni fun a =
  ( Show fun
  , Everywhere uni (ComposeC Show AsCoq)
  , GShow (AsCoqUni uni)
  )

-- * Instances for type universes

instance Closed uni => Closed (AsCoqUni uni) where
    type AsCoqUni uni `Everywhere` constr = uni `Everywhere` ComposeC constr AsCoq

    bring
        :: forall constr a r proxy. uni `Everywhere` ComposeC constr AsCoq
        => proxy constr -> AsCoqUni uni (Esc a) -> (constr a => r) -> r
    bring _ (AsCoqUni uni) r = bring (Proxy @(ComposeC constr AsCoq)) uni r

    encodeUni (AsCoqUni uni) = encodeUni uni

    withDecodedUni k = withDecodedUni $ \uni -> k (AsCoqUni uni)

instance GShow (AsCoqUni DefaultUni) where
    gshowsPrec pr (AsCoqUni a) = showsPrec pr a

deriving newtype instance Show (AsCoq Integer)
deriving newtype instance Show (AsCoq ())
deriving newtype instance Show (AsCoq Bool)
deriving via [AsCoq a] instance Show (AsCoq a) => Show (AsCoq [a])
deriving via (AsCoq a, AsCoq b) instance (Show (AsCoq a), Show (AsCoq b)) => Show (AsCoq (a, b))
deriving newtype instance Show (AsCoq Data)
deriving newtype instance Show (AsCoq BLS12_381.G1.Element)
deriving newtype instance Show (AsCoq BLS12_381.G2.Element)
deriving newtype instance Show (AsCoq BLS12_381.Pairing.MlResult)
instance Show (AsCoq Text) where
    showsPrec p (AsCoq text) = showsPrec p (map AsCoq (unpack $ Text.encodeUtf8 text))
instance Show (AsCoq Word8) where
    -- Matches constructor notation of Coq.Init.Byte
    showsPrec _p (AsCoq w) = printf "x%02x" w
instance Show (AsCoq ByteString) where
    showsPrec p (AsCoq bs) = showsPrec p (map AsCoq (unpack bs))

-- * Names
-- These instances mimic GHC derived show instances, if they were defined without record syntax.

instance Show (AsCoq Name) where
  showsPrec p (AsCoq (Name x y)) =
    showParen (p >= 11) $
      showString "Name" .
      showString " " .
      showsPrec 11 (AsCoq x) .
      showString " " .
      showsPrec 11 (AsCoq y)

instance Show (AsCoq TyName) where
  showsPrec p (AsCoq (TyName x)) =
    showParen (p >= 11) $
      showString "TyName" .
      showString " " .
      showsPrec 11 (AsCoq x)

instance Show (AsCoq Unique) where
  showsPrec p (AsCoq (Unique n)) =
    showParen (p >= 11) $
      showString "Unique" .
      showString " " .
      showsPrec 11 n

instance
  ( Show (AsCoq tyname)
  , Show (AsCoq name)
  , GShow (AsCoqUni uni)
  , Closed uni, AsCoqUni uni `Everywhere` Show
  , Show fun
  , Show ann
  ) => Show (AsCoq (Term tyname name uni fun ann)) where
    showsPrec pr (AsCoq term) =
      showsPrec pr .
      mapName AsCoq .
      mapTyName AsCoq .
      mapUni fTy fConst $
        term
      where
        fConst (Some (ValueOf uni x)) = Some (ValueOf (AsCoqUni uni) (AsCoq x))
        fTy (SomeTypeIn ty) = SomeTypeIn (AsCoqUni ty)


