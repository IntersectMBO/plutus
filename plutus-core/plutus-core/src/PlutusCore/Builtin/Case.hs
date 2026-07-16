{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module PlutusCore.Builtin.Case where

import PlutusCore.Builtin.KnownType (HeadSpine (..))
import PlutusCore.Core.Type (Type, UniOf)
import PlutusCore.Name.Unique (TyName)
import PlutusPrelude

import Control.DeepSeq (NFData (..), rwhnf)
import Control.Monad.ST (ST)
import Data.Text (Text)
import Data.Vector (Vector)
import NoThunks.Class
import Universe

class AnnotateCaseBuiltin uni where
  {-| Given a tag for a built-in type and a list of branches, annotate each of the branches with
  its expected argument types or fail if casing on values of the built-in type isn't supported.
  Note: you don't need to include the resulting type of the whole case matching in the
  returning list here. -}
  annotateCaseBuiltin
    :: UniOf term ~ uni
    => Type TyName uni ann
    -> [term]
    -> Either Text [(term, [Type TyName uni ann])]

class CaseBuiltin uni where
  {-| Given a constant with its type tag and a vector of branches, choose the appropriate branch
  or fail if the constant doesn't correspond to any of the branches (or casing on constants of
  this type isn't supported at all). -}
  caseBuiltin
    :: UniOf term ~ uni
    => Some (ValueOf uni)
    -> Vector term
    -> HeadSpine Text term (Some (ValueOf uni))

  {-# MINIMAL caseBuiltin #-}

{-| A non-negative amount of pattern-matcher work. The constructors distinguish bounded work with
materially different execution costs without storing a measure in the pattern AST.

'PatternWork' covers cheap root/scalar work, bytestring words, and reached captures.
'PatternStructuralWork' covers one reached child/field edge, including child dispatch and its
bounded exact-arity probe.
'PatternFailureWork' covers abandoning a failed alternative and probing the next one; the matcher
spends it after a mismatch is known but before performing that transition and probe. -}
data PatternWork
  = PatternWork !Word64
  | PatternStructuralWork
  | PatternFailureWork

{-| The fixed effect used by universe-specific pattern matchers. It is a Reader over 'ST': the CEK
supplies its budget action once when running the matcher, while matcher code calls
'spendPatternWork' directly from its monadic context. Keeping the monad fixed lets GHC erase the
Reader and 'ST' newtypes and optimize sequencing without a per-step unknown-'Monad' dictionary. -}
newtype PatternMatchM s a = PatternMatchM
  { runPatternMatchM :: (PatternWork -> ST s ()) -> ST s a
  }

instance Functor (PatternMatchM s) where
  fmap f (PatternMatchM action) = PatternMatchM $ \spend -> fmap f (action spend)
  {-# INLINE fmap #-}

instance Applicative (PatternMatchM s) where
  pure value = PatternMatchM $ \_ -> pure value
  {-# INLINE pure #-}
  PatternMatchM fun <*> PatternMatchM arg =
    PatternMatchM $ \spend -> fun spend <*> arg spend
  {-# INLINE (<*>) #-}

instance Monad (PatternMatchM s) where
  PatternMatchM action >>= next =
    PatternMatchM $ \spend -> action spend >>= \value -> runPatternMatchM (next value) spend
  {-# INLINE (>>=) #-}

spendPatternWork :: PatternWork -> PatternMatchM s ()
spendPatternWork work = PatternMatchM $ \spend -> spend work
{-# INLINE spendPatternWork #-}

class MatchBuiltin uni pat where
  {-| Given a built-in constant and an ordered vector of pattern/handler alternatives, choose the
  first matching handler while paying incrementally through 'spendPatternWork'. The CEK supplies
  the concrete budget action when it runs the resulting 'PatternMatchM'.

  Spending is a strict sequencing boundary: the matcher must call 'spendPatternWork' before the
  work charged to it. In particular, no pattern or value traversal, field advance, native
  comparison, capture allocation or materialization, or pending-work resume may happen before its
  corresponding spend. Any input-sized native operation must be preceded by a charge that bounds
  the complete operation from information already available in the pattern.

  Work between spends must be a documented bounded quantum. Exact lists, for example, must be
  streamed alongside their child patterns with a spend before each reached field edge; the final
  edge can include the bounded exact-arity probe. They must not be traversed with 'length'. Early
  mismatch stops without paying for unreachable pattern work. Each reached capture is charged
  before it is retained. That charge covers both its later strict 'Spine' materialization and its
  implicit application to the selected handler, even when a subsequent mismatch abandons the
  capture. Other charges cover only the immediately following bounded operation.

  Alternative ordering and selection belong to the universe matcher, not the CEK machine. A
  successful matcher returns the selected handler and captures directly in head-spine form and
  handler-application order. 'HeadError' represents an unsupported matcher or exhaustion of the
  alternatives. The 'PatternMatchM' context is a trusted costing boundary. -}
  matchBuiltin
    :: Some (ValueOf uni)
    -> Vector (pat, term)
    -> PatternMatchM s (HeadSpine Text term (Some (ValueOf uni)))
  matchBuiltin _ _ =
    pure $ HeadError "built-in patterns are not supported by this universe"

-- See Note [DO NOT newtype-wrap functions].
{-| A @data@ version of 'CaseBuiltin'. we parameterize the evaluator by a 'CaserBuiltin' so that
the caller can choose whether to use the 'caseBuiltin' method or the always failing caser (the
latter is required for earlier protocol versions when we didn't support casing on builtins). -}
data CaserBuiltin uni = CaserBuiltin
  { unCaserBuiltin
      :: !( forall term
             . UniOf term ~ uni => Some (ValueOf uni) -> Vector term -> HeadSpine Text term (Some (ValueOf uni))
          )
  }

{-| A data version of 'MatchBuiltin'. It is separate from 'CaserBuiltin' so that adding a pattern
language to UPLC does not parameterize the typed CK machine or change legacy built-in casing APIs. -}
data MatcherBuiltin uni pat = MatcherBuiltin
  { unMatchBuiltin
      :: !( forall s term
             . Some (ValueOf uni)
            -> Vector (pat, term)
            -> PatternMatchM s (HeadSpine Text term (Some (ValueOf uni)))
          )
  }

instance NFData (CaserBuiltin uni) where
  rnf = rwhnf

deriving via
  OnlyCheckWhnfNamed "PlutusCore.Builtin.Case.CaserBuiltin" (CaserBuiltin uni)
  instance
    NoThunks (CaserBuiltin uni)

instance NFData (MatcherBuiltin uni pat) where
  rnf = rwhnf

deriving via
  OnlyCheckWhnfNamed "PlutusCore.Builtin.Case.MatcherBuiltin" (MatcherBuiltin uni pat)
  instance
    NoThunks (MatcherBuiltin uni pat)

availableCaserBuiltin :: CaseBuiltin uni => CaserBuiltin uni
availableCaserBuiltin = CaserBuiltin caseBuiltin

availableMatcherBuiltin
  :: MatchBuiltin uni pat => MatcherBuiltin uni pat
availableMatcherBuiltin = MatcherBuiltin matchBuiltin

instance CaseBuiltin uni => Default (CaserBuiltin uni) where
  def = availableCaserBuiltin

instance MatchBuiltin uni pat => Default (MatcherBuiltin uni pat) where
  def = availableMatcherBuiltin

unavailableCaserBuiltin :: Int -> CaserBuiltin uni
unavailableCaserBuiltin ver =
  CaserBuiltin
    ( \_ _ ->
        HeadError $
          "'case' on values of built-in types is not supported in protocol version " <> display ver
    )

unavailableMatcherBuiltin :: Int -> MatcherBuiltin uni pat
unavailableMatcherBuiltin ver =
  MatcherBuiltin
    ( \_ _ ->
        pure . HeadError $
          "patterns on values of built-in types are not supported in protocol version " <> display ver
    )
