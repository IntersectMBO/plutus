{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Instances for 'Data.Row.Records.Rec' and 'Data.Row.Variants.Var' types
module Data.Row.Extras(
      JsonRec(..)
    , JsonVar(..)
    , MonoidRec(..)
    , namedBranchFromJSON
    ) where

import           Data.Aeson            (FromJSON, ToJSON, (.:), (.=))
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
    parseJSON vl = fmap JsonVar $ do
      Aeson.withObject "Var" (\obj -> do
        theTag <- obj .: "tag"
        theValue <- obj .: "value"
        namedBranchFromJSON theTag theValue)
        vl

instance Forall s ToJSON => ToJSON (JsonVar s) where
    toJSON (JsonVar v) =
      let (lbl, vl) = Variants.eraseWithLabels @ToJSON @s  @Text @Aeson.Value Aeson.toJSON v
      in Aeson.object ["tag" .= lbl, "value" .= vl]

newtype JsonRec s = JsonRec { unJsonRec :: Rec s }

-- | Parse a 'Var s' from JSON if the label of the branch is known.
namedBranchFromJSON :: forall s. (AllUniqueLabels s, Forall s FromJSON) => String -> Aeson.Value -> Aeson.Parser (Var s)
namedBranchFromJSON nm vl =
  Variants.fromLabels @FromJSON @s @Aeson.Parser (\case { n | show n == nm -> Aeson.parseJSON vl; _ -> fail "Wrong label" })

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

