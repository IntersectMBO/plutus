{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Instances for 'Data.Row.Records.Rec' and 'Data.Row.Variants.Var' types
module Data.Row.Extras(
      JsonRec(..)
    , JsonVar(..)
    , MonoidRec(..)
    ) where

import           Data.Aeson            (FromJSON, ToJSON, (.:))
import qualified Data.Aeson            as Aeson
import qualified Data.Aeson.Types      as Aeson
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Proxy            (Proxy (..))
import           Data.Row
import           Data.Row.Internal
import qualified Data.Row.Records      as Records
import qualified Data.Row.Variants     as Variants
import           Data.Text             (Text)
import qualified Data.Text             as Text

newtype JsonVar s = JsonVar { unJsonVar :: Var s }

instance (AllUniqueLabels s, Forall s FromJSON) => FromJSON (JsonVar s) where
    parseJSON vl = JsonVar <$> Variants.fromLabels @FromJSON @s @Aeson.Parser (\lbl -> Aeson.withObject "Var" (\obj -> do { tg <- obj .: "tag"; if tg == show lbl then (obj .: "value") >>= Aeson.parseJSON else fail "Wrong label" }) vl)

instance Forall s ToJSON => ToJSON (JsonVar s) where
    toJSON (JsonVar v) = Aeson.object [Variants.eraseWithLabels @ToJSON @s  @Text @Aeson.Value Aeson.toJSON v]

newtype JsonRec s = JsonRec { unJsonRec :: Rec s }

instance Forall s ToJSON => ToJSON (JsonRec s) where
  toJSON = Aeson.object . Records.eraseWithLabels @ToJSON @s @Text @Aeson.Value Aeson.toJSON . unJsonRec

instance (AllUniqueLabels s, Forall s FromJSON) => FromJSON (JsonRec s) where
  parseJSON vl = JsonRec <$> Records.fromLabelsA @FromJSON @Aeson.Parser @s  (\lbl -> Aeson.withObject "Rec" (\obj -> obj .: (Text.pack $ show lbl) >>= Aeson.parseJSON) vl)

newtype MonoidRec s = MonoidRec { unMonoidRec :: Rec s }

instance Forall s Semigroup => Semigroup (MonoidRec s) where
  (<>) = merge @s

instance (AllUniqueLabels s, Forall s Semigroup, Forall s Monoid) => Monoid (MonoidRec s) where
  mempty = MonoidRec (Records.default' @Monoid @s mempty)
  mappend = (<>)

merge :: forall s. Forall s Semigroup => MonoidRec s -> MonoidRec s -> MonoidRec s
merge (MonoidRec rec1) (MonoidRec rec2) = MonoidRec $ metamorph @_ @s @Semigroup @(Product Rec Rec) @Rec @Identity Proxy doNil doUncons doCons (Pair rec1 rec2)
  where
    doNil _ = empty
    -- unsafeRemove and unsafeInjectFront are OK to use here
    -- cf. documentation at https://hackage.haskell.org/package/row-types-0.3.0.0/docs/Data-Row-Records.html
    doUncons l (Pair r1 r2) = (Identity $ r1 .! l <> r2 .! l, Pair (Records.unsafeRemove l r1) (Records.unsafeRemove l r2))
    doCons l (Identity v) = Records.unsafeInjectFront l v

