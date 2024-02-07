{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Simplify (
    simplifyTerm,
    simplifyProgram,
    SimplifyOpts (..),
    soMaxSimplifierIterations,
    soMaxCseIterations,
    soInlineHints,
    soConservativeOpts,
    defaultSimplifyOpts,
    InlineHints (..),
) where

import PlutusCore.Compiler.Types
import PlutusCore.Default qualified as PLC
import PlutusCore.Default.Builtins
import PlutusCore.Name
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Transform.CaseOfCase
import UntypedPlutusCore.Transform.CaseReduce
import UntypedPlutusCore.Transform.Cse
import UntypedPlutusCore.Transform.FloatDelay
import UntypedPlutusCore.Transform.ForceDelay
import UntypedPlutusCore.Transform.Inline

import Control.Lens.TH
import Control.Monad
import Data.List
import Data.Typeable
import UntypedPlutusCore.Transform.ForceCase (forceCase)

data SimplifyOpts name a = SimplifyOpts
    { _soMaxSimplifierIterations :: Int
    , _soMaxCseIterations        :: Int
    , _soConservativeOpts        :: Bool
    , _soInlineHints             :: InlineHints name a
    }
    deriving stock (Show)

makeLenses ''SimplifyOpts

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts =
    SimplifyOpts
        { _soMaxSimplifierIterations = 12
        , _soMaxCseIterations = 4
        , _soConservativeOpts = False
        , _soInlineHints = mempty
        }

simplifyProgram ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    Program name uni fun a ->
    m (Program name uni fun a)
simplifyProgram opts (Program a v t) = Program a v <$> simplifyTerm opts t

simplifyTerm ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    Term name uni fun a ->
    m (Term name uni fun a)
simplifyTerm opts =
    simplifyNTimes (_soMaxSimplifierIterations opts) >=> cseNTimes cseTimes
  where
    -- Run the simplifier @n@ times
    simplifyNTimes :: Int -> Term name uni fun a -> m (Term name uni fun a)
    simplifyNTimes n = foldl' (>=>) pure $ map simplifyStep [1..n]

    -- Run CSE @n@ times, interleaved with the simplifier.
    -- See Note [CSE]
    cseNTimes :: Int -> Term name uni fun a -> m (Term name uni fun a)
    cseNTimes n = foldl' (>=>) pure $ concatMap (\i -> [cseStep i, simplifyStep i]) [1..n]

    -- generate simplification step
    simplifyStep :: Int -> Term name uni fun a -> m (Term name uni fun a)
    simplifyStep _ =
        floatDelay
            >=> pure . forceCase
            >=> pure . forceDelayCancel
            >=> pure . caseOfCase'
            >=> pure . caseReduce
            >=> inline (_soInlineHints opts)

    caseOfCase' :: Term name uni fun a -> Term name uni fun a
    caseOfCase' = case eqT @fun @DefaultFun of
        Just Refl -> caseOfCase
        Nothing   -> id

    cseStep :: Int -> Term name uni fun a -> m (Term name uni fun a)
    cseStep _ = case (eqT @name @Name, eqT @uni @PLC.DefaultUni) of
        (Just Refl, Just Refl) -> cse
        _                      -> pure

    cseTimes = if _soConservativeOpts opts then 0 else _soMaxCseIterations opts
