-- editorconfig-checker-disable-file
{-# LANGUAGE TemplateHaskell #-}
module UntypedPlutusCore.Simplify ( simplifyTerm, simplifyProgram, SimplifyOpts (..), soMaxSimplifierIterations, soInlineHints, defaultSimplifyOpts, InlineHints (..) ) where

import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Transform.CaseReduce
import UntypedPlutusCore.Transform.ForceDelay
import UntypedPlutusCore.Transform.Inline

import Control.Monad
import Data.List
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote

import Control.Lens.TH

data SimplifyOpts name a = SimplifyOpts { _soMaxSimplifierIterations  :: Int, _soInlineHints :: InlineHints name a }
  deriving stock (Show)

makeLenses ''SimplifyOpts

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts = SimplifyOpts
    { _soMaxSimplifierIterations = 12
    , _soInlineHints = mempty
    }

simplifyProgram
    :: forall name uni fun m a
    . (PLC.ToBuiltinMeaning uni fun, MonadQuote m, HasUnique name TermUnique, Eq name)
    => SimplifyOpts name a
    -> Program name uni fun a
    -> m (Program name uni fun a)
simplifyProgram opts (Program a v t) = Program a v <$> simplifyTerm opts t

simplifyTerm
    :: forall name uni fun m a
    . (PLC.ToBuiltinMeaning uni fun, MonadQuote m, HasUnique name TermUnique, Eq name)
    => SimplifyOpts name a
    -> Term name uni fun a
    -> m (Term name uni fun a)
simplifyTerm opts = simplifyNTimes (_soMaxSimplifierIterations opts)
    where
        -- Run the simplifier @n@ times
        simplifyNTimes :: Int -> Term name uni fun a -> m (Term name uni fun a)
        simplifyNTimes n = foldl' (>=>) pure (map simplifyStep [1 .. n])
        -- generate simplification step
        simplifyStep :: Int -> Term name uni fun a -> m (Term name uni fun a)
        simplifyStep _ term = inline (_soInlineHints opts) (caseReduce $ forceDelayCancel term)
