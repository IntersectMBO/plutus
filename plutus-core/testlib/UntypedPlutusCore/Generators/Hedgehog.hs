module UntypedPlutusCore.Generators.Hedgehog where

import UntypedPlutusCore

import Control.Lens (andOf, to)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Universe

discardIfAnyConstant
  :: MonadGen m
  => (Some (ValueOf uni) -> Bool)
  -> m (Program name uni fun ann)
  -> m (Program name uni fun ann)
discardIfAnyConstant p = Gen.filterT . andOf $ progTerm . termConstantsDeep . to (not . p)
