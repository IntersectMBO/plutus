{-# LANGUAGE LambdaCase #-}

{- | The Float Delay optimization floats `Delay` from arguments into function bodies,
if possible. It turns @(\n -> ...Force n...Force n...) (Delay arg)@ into
@(\n -> ...Force (Delay n)...Force (Delay n)...) arg@.

The above transformation is performed if:

    * All occurrences of @arg@ are under @Force@.

    * @arg@ is essentially work-free.

This achieves a similar effect to Plutonomy's "Split Delay" optimization. The difference
is that Split Delay simply splits the @Delay@ argument into multiple arguments, turning the
above example into @(\m -> (\n -> ...Force n...Force n...) (Delay m)) arg@, and then relies
on other optimizations to simplify it further. Specifically, once the inliner inlines
@Delay m@, it will be identical to the result of Float Delay.

The advantages of Float Delay are:

    * It doesn't rely on the inliner. In this example, Split Delay relies on the inliner to
      inline @Delay m@, but there's no guarantee that the inliner will do so, because inlining
      it may increase the program size.

      We can potentially modify the inliner such that it is aware of Float Delay and
      Force-Delay Cancel, and makes inlining decisions with these other optimizations in mind.
      The problem is that, not only does this makes the inlining heuristics much more
      complex, but it could easily lead to code duplication. Other optimizations often
      need to do some calculation in order to make certain optimization decisions (e.g., in
      this case, we want to check whether all occurrences of @arg@ are under @Force@), and
      if we rely on the inliner to inline the @Delay@, then the same check would need to be
      performed by the inliner.

    * Because Force Delay requires that all occurrences of @arg@ are under @Force@, it
      guarantees to not increase the size or the cost of the program. This is not the case
      with Split Delay: in this example, if the occurrences of @n@ are not under @Force@,
      then Split Delay may increase the size of the program, regardless of whether or not
      @Delay m@ is inlined. If @Delay m@ is not inlined, then it will also increase the
      cost of the program, due to the additional application.

The alternative approach that always floats the @Delay@ regardless of whether or not all
occurences of @arg@ are under @Force@ was implemented and tested, and it is strictly worse than
Float Delay on our current test suite (specifically, Split Delay causes one test case
to have a slightly bigger program, and everything else is equal).

Why is this optimization performed on UPLC, not PIR?

    1. Not only are the types and let-bindings in PIR not useful for this optimization,
       they can also get in the way. For example, we cannot transform
       @let f = /\a. ...a... in ...{f t1}...{f t2}...@ into
       @ket f = ...a... in ...f...f...@.

    2. This optimization mainly interacts with ForceDelayCancel and the inliner, and
       both are part of the UPLC simplifier.
-}
module UntypedPlutusCore.Transform.FloatDelay (floatDelay) where

import PlutusCore qualified as PLC
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Name.UniqueMap qualified as UMap
import PlutusCore.Name.UniqueSet qualified as USet
import UntypedPlutusCore.Core.Plated (termSubterms)
import UntypedPlutusCore.Core.Type (Term (..))
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (FloatDelay), SimplifierT,
                                               recordSimplification)

import Control.Lens (forOf, forOf_, transformOf)
import Control.Monad.Trans.Writer.CPS (Writer, execWriter, runWriter, tell)

floatDelay ::
  ( PLC.MonadQuote m
  , PLC.Rename (Term name uni fun a)
  , PLC.HasUnique name PLC.TermUnique
  ) =>
  Term name uni fun a ->
  SimplifierT name uni fun a m (Term name uni fun a)
floatDelay term = do
  result <-
    PLC.rename term >>= \t ->
        pure . uncurry (flip simplifyBodies) $ simplifyArgs (unforcedVars t) t
  recordSimplification term FloatDelay result
  return result

{- | First pass. Returns the names of all variables, at least one occurrence
of which is not under `Force`.
-}
unforcedVars ::
  forall name uni fun a
  . (PLC.HasUnique name PLC.TermUnique)
  => Term name uni fun a
  -> PLC.UniqueSet PLC.TermUnique
unforcedVars = execWriter . go
  where
    go :: Term name uni fun a -> Writer (PLC.UniqueSet PLC.TermUnique) ()
    go = \case
      Var _ n       -> tell (USet.singletonName n)
      Force _ Var{} -> pure ()
      t             -> forOf_ termSubterms t go

{- | Second pass. Removes `Delay` from eligible arguments, and returns
the names of variables whose corresponding arguments are modified.
-}
simplifyArgs ::
  forall name uni fun a.
  (PLC.HasUnique name PLC.TermUnique) =>
  -- | The set of variables returned by `unforcedVars`.
  PLC.UniqueSet PLC.TermUnique ->
  Term name uni fun a ->
  (Term name uni fun a, PLC.UniqueMap PLC.TermUnique a)
simplifyArgs blacklist = runWriter . go
  where
    go :: Term name uni fun ann -> Writer (PLC.UniqueMap PLC.TermUnique ann) (Term name uni fun ann)
    go = \case
      Apply appAnn (LamAbs lamAnn n lamBody) (Delay delayAnn arg)
        | isEssentiallyWorkFree arg
        , n `USet.notMemberByName` blacklist -> do
            tell (UMap.singletonByName n delayAnn)
            (Apply appAnn . LamAbs lamAnn n <$> go lamBody) <*> go arg
      t -> forOf termSubterms t go

-- | Third pass. Turns @Force n@ into @Force (Delay n)@ for all eligibile @n@.
simplifyBodies
  :: (PLC.HasUnique name PLC.TermUnique)
  => PLC.UniqueMap PLC.TermUnique a
  -> Term name uni fun a
  -> Term name uni fun a
simplifyBodies whitelist = transformOf termSubterms $ \case
  var@(Var _ n)
    | Just ann <- UMap.lookupName n whitelist -> Delay ann var
  t -> t

{- | Whether evaluating the given `Term` is pure and essentially work-free
(barring the CEK machine overhead).
-}

--- This should be the erased version of 'PlutusIR.Transform.LetFloat.isEssentiallyWorkFree'.
isEssentiallyWorkFree :: Term name uni fun a -> Bool
isEssentiallyWorkFree = \case
  LamAbs{}   -> True
  Constant{} -> True
  Delay{}    -> True
  Constr{}   -> True
  Builtin{}  -> True
  Let{}      -> True
  Var{}      -> False
  Force{}    -> False
  -- Unsaturated builtin applications should also be essentially work-free,
  -- but this is currently not implemented for UPLC.
  -- `UntypedPlutusCore.Transform.Inline.isPure` has the same problem.
  Apply{}    -> False
  Case{}     -> False
  Error{}    -> False
  Bind{}     -> False
