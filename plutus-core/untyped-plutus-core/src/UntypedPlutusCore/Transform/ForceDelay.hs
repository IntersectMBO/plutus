{- Note [Cancelling interleaved Force-Delay pairs]

 The 'ForceDelay' optimisation pushes 'Force' inside its direct 'Apply' subterms,
 removing any 'Delay' at the top of the body of the underlying lambda abstraction.
 For example, @force [(\x -> delay b) a]@ is transformed into @[(\x -> b) a]@.
 We also consider the case where the 'Force' is applied directly to the 'Delay' as
 the base case, i.e. the case when the applications of lambdas is empty.
 In such simple cases, the transformation is obviously correct, the question remains
 if this approach can be generalised (note: see remark at the bottom).

 Since UPLC programs are created from erasing the types of TPLC programs (see
 "PlutusCore.Compiler.Erase") we will consider TPLC terms of the following structure,
 in pseudo-code (@/\@ is (multi-)type abstraction and @\@ is (multi-)term abstraction):

 > /\T1 -> \X1 -> /\T2 -> \X2 -> /\T3 -> \X3 -> ... -> /\Tn -> \Xn -> body

 where @T1 ... Tn@ are lists of type variables (e.g. @T1@ could be @[t, q, p]@)
 and @X1 ... Xn@ are lists of term variables. Of course, each @/\@ and @\@ here would
 desugar to a sequence of type/term abstractions. Also @[ M P Q ]@ is iterated
 term application, which, as usual, is left-associative.

 In order to reason about the proposed optimisation we need to consider such terms in
 the context of them being applied to some sequence of terms.

 One important observation is that this transformation requires that the underlying
 (term)-lambda abstraction will be exactly reduced by the applications.
 For UPLC, this can happen only when the number of lambda abstracted variables is equal
 to the number of terms to which it will be applied.
 For example, @force (\\x -> delay b) => (\\x -> b)@ is invalid, since the former is @error@.
 The other case, we can see that applying the optimisation modifies the end result:
 >  force [(\x -> delay b) a1 a2] => [(\x -> b) a1 a2] => b[x1:=a1] a2
 >
 >  vs.
 >
 >  force [(\x -> delay b) a1 a2] => force [(delay b[x1:=a1]) a2] => error

 To generalise, we consider the family of terms above applied to a family of types and
 terms:
 > [ (/\T1 -> \X1 ->  ... -> /\Tn -> \Xn -> body)
 >     T1 X1 ... Tn Xn
 > ]

 For brevity, the types and the terms to which the lambda applies are named the same as the
 bound variables, but of course this isn't necessary.
 Also note that in general @|Ti| == |Xi|@ doesn't necessarily hold for any @i in [1, n]@.

 Translated to UPLC, the original term is:
 >  delay^|T1| (\X1 -> delay^|T2| (\X2 -> delay^|T3| (\X3 -> ... -> delay^|Tn| (\Xn -> body))))
 where @delay^|A|@ means "apply delay |A| (the length of A) times".

 With the applications:
 > [force^|Tn| (... [force^|T3| ([force^|T2| ([force^|T1| (original) X1]) X2]) X3] ...) Xn]

 After inlining @original@ we get:
 >  [force^|Tn|
 >    (...
 >      ([force^|T3|
 >        ([force^|T2|
 >          ([force^|T1|
 >            (delay^|T1|
 >              (\X1 ->
 >                 delay^|T2| (\X2 ->
 >                   delay^|T3| (\X3 ->
 >                     ... ->
 >                       delay^|Tn| (\Xn -> body)))))
 >           X1]) X2]) X3]) ...) Xn]

 In the end, after applying the base case optimisation:
 >  [force^|Tn|
 >    (...
 >      ([force^|T3|
 >        ([force^|T2|
 >          ([(\X1 ->
 >            delay^|T2| (\X2 ->
 >              delay^|T3| (\X3 ->
 >                ... ->
 >                  delay^|Tn| (\Xn -> body))))
 >          X1]) X2]) X3]) ...) Xn]

 Notice that the next two reduction steps (applying @X1@ and reducing @force (delay ...)@)
 produce an equivalent term to applying the transformation and then the reduction rule
 for application.
 This is easy to check, so we continue by showing what the "optimised term" looks like:
 >  [force^|Tn|
 >    (...
 >      [force^|T3|
 >        ([(\X1 -> \X2 ->
 >          delay^|T3| (\X3 ->
 >            ... ->
 >              delay^|Tn| (\Xn -> body)))
 >         X1 X2]) X3] ...) Xn]

 The term can be optimised further by "erasing" the @force^|T3|@ and @delay^|T3|@ pair,
 and so on until @Tn@.

 For examples of terms we can optimise, see the test cases in the
 "Transform.Simplify.forceDelay*" module of the test suite.

 Remark:

 It has been observed that the transformation:
 > force([(\x -> body) 5])
 > ==>
 > [(\x -> force(body))]
 where @body@ isn't necessarily of the form @delay(...)@ is also valid.
 The question arises, can we generalise the algorithm above given this observation?

 Let's consider a version of this algorithm which only "pushes forces" down under the
 applications of lambdas, and the following term:
 > force (force ([(\x1 -> delay [(\x2 -> delay [(\x3 -> body) 5]) 7]) 9]))
 > ==> (push inner force)
 > force ([(\x1 -> force (delay [(\x2 -> delay [(\x3 -> body) 5]) 7]) 9])
 > ==> (push outer force)
 > [(\x1 -> force (force (delay [(\x2 -> delay [(\x3 -> body) 5]) 7])) 9]

 The algorithm gets stuck because after this step the term doesn't contain a direct
 application of a @force@ over a series of lambdas and applications.
 To proceed, we need to introduce a separate pass which removes forces immediately
 followed by delays. For our example above this results in:
 > [(\x1 -> force ([(\x2 -> delay [(\x3 -> body) 5]) 7])) 9]

 As can be seen, to proceed with simplifying the term we need to run the "push" pass
 again.

 For an arbitrary term to be fully reduced by such an algorithm, we would need to also do
 an arbitrary number of traversals in this optimisation procedure. This increases the complexity
 of the simplifier from both a computational perspective and a human-readability perspective.

 We can easily avoid this situation by removing the force-delay pairs in the same pass.
 This means that we can fully reduce the term in a single traversal of the term, as described
 in the original algorithm.

 We also turn

 > (force [ (force (builtin ifThenElse)) b (delay x) (delay y) ] )

 into

 > [ (force (builtin ifThenElse)) b x y ]

 if both @x@ and @y@ are pure and work-free.
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module UntypedPlutusCore.Transform.ForceDelay
  ( forceDelay
  ) where

import PlutusCore.Builtin (BuiltinSemanticsVariant)
import PlutusCore.Default (DefaultFun (IfThenElse), DefaultUni)
import PlutusCore.MkPlc (mkIterApp)
import UntypedPlutusCore.Core
import UntypedPlutusCore.Purity (isPure, isWorkFree)
import UntypedPlutusCore.Transform.Simplifier
  ( SimplifierStage (..)
  , SimplifierT
  , recordSimplification
  )

import Control.Lens (transformOf)
import Control.Monad (guard)
import Data.Foldable as Foldable (foldl')

{-| Traverses the term, for each node applying the optimisation
 detailed above. For implementation details see 'optimisationProcedure'. -}
forceDelay
  :: (uni ~ DefaultUni, fun ~ DefaultFun, Monad m)
  => BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
forceDelay semVar term = do
  let result = transformOf termSubterms (processTerm semVar) term
  recordSimplification term CaseOfCase result
  return result

{-| Checks whether the term is of the right form, and "pushes"
 the 'Force' down into the underlying lambda abstractions. -}
processTerm
  :: (uni ~ DefaultUni, fun ~ DefaultFun)
  => BuiltinSemanticsVariant fun -> Term name uni fun a -> Term name uni fun a
processTerm semVar = \case
  Force _ (Delay _ t) -> t
  -- Remove @Delay@s from @ifThenElse@ branches if the latter is @Force@d and the delayed term are
  -- pure and work-free anyway.
  Force
    _
    ( splitApplication ->
        ( forceIfThenElse@(Force _ (Builtin _ IfThenElse))
          , [cond, (trueAnn, (Delay _ trueAlt)), (falseAnn, (Delay _ falseAlt))]
          )
      )
      | all (\alt -> isPure semVar alt && isWorkFree semVar alt) [trueAlt, falseAlt] ->
          mkIterApp
            forceIfThenElse
            [cond, (trueAnn, trueAlt), (falseAnn, falseAlt)]
  original@(Force _ subTerm) ->
    case optimisationProcedure subTerm of
      Just result -> result
      Nothing -> original
  t -> t

{-| Converts the subterm of a 'Force' into specialised types for representing
 multiple applications on top of multiple abstractions. Checks whether the lambda
 will eventually get "exactly reduced" and applies the optimisation.
 Returns 'Nothing' if the optimisation cannot be applied. -}
optimisationProcedure :: Term name uni fun a -> Maybe (Term name uni fun a)
optimisationProcedure term = do
  asMultiApply <- toMultiApply term
  innerMultiAbs <- toMultiAbs . appHead $ asMultiApply
  guard $ length (appSpineRev asMultiApply) == length (absVars innerMultiAbs)
  case absRhs innerMultiAbs of
    Delay _ subTerm ->
      let optimisedInnerMultiAbs = innerMultiAbs {absRhs = subTerm}
          optimisedMultiApply =
            asMultiApply {appHead = fromMultiAbs optimisedInnerMultiAbs}
       in pure . fromMultiApply $ optimisedMultiApply
    _ -> Nothing

data MultiApply name uni fun a = MultiApply
  { appHead :: Term name uni fun a
  , appSpineRev :: [(a, Term name uni fun a)]
  }

toMultiApply :: Term name uni fun a -> Maybe (MultiApply name uni fun a)
toMultiApply term =
  case term of
    Apply _ _ _ -> run [] term
    _ -> Nothing
  where
    run acc (Apply a t1 t2) =
      run ((a, t2) : acc) t1
    run acc t =
      pure $ MultiApply t acc

fromMultiApply :: MultiApply name uni fun a -> Term name uni fun a
fromMultiApply (MultiApply term ts) =
  Foldable.foldl' (\acc (ann, arg) -> Apply ann acc arg) term ts

data MultiAbs name uni fun a = MultiAbs
  { absVars :: [(a, name)]
  , absRhs :: Term name uni fun a
  }

toMultiAbs :: Term name uni fun a -> Maybe (MultiAbs name uni fun a)
toMultiAbs term =
  case term of
    LamAbs _ _ _ -> run [] term
    _ -> Nothing
  where
    run acc (LamAbs a name t) =
      run ((a, name) : acc) t
    run acc t =
      pure $ MultiAbs acc t

fromMultiAbs :: MultiAbs name uni fun a -> Term name uni fun a
fromMultiAbs (MultiAbs vars term) =
  Foldable.foldl' (\acc (ann, name) -> LamAbs ann name acc) term vars
