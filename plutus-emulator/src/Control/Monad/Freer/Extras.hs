{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Control.Monad.Freer.Extras where

import           Control.Lens
import qualified Control.Monad.Except         as MTL
import           Control.Monad.Freer
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Internal
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer
import qualified Control.Monad.State          as MTL

{- Note [Various raising helpers]
These are all to help with the issue where you have something of type

Eff effs a

where effs is some *fixed* list of effects. You may then need to insert
more effects *under* effs to interpret them in terms of. It turns out that
inserting effects at the *end* of the list is tricky.

I have no idea what I'm doing, these are partially stolen from freer-simple/polysemy
with a lot of hacking around.
-}


weakenEnd :: forall effs a . Union '[a] ~> Union (a ': effs)
weakenEnd u = inj (extract u)

weakenEnd2 :: forall effs a b . Union '[a, b] ~> Union (a ': b ': effs)
weakenEnd2 u = case decomp u of
    Left u' -> weaken $ weakenEnd u'
    Right t -> inj t

weakenEnd3 :: forall effs a b c . Union '[a, b, c] ~> Union (a ': b ': c ': effs)
weakenEnd3 u = case decomp u of
    Left u' -> weaken $ weakenEnd2 u'
    Right t -> inj t

weakenEnd4 :: forall effs a b c d. Union '[a, b, c, d] ~> Union (a ': b ': c ': d ': effs)
weakenEnd4 u = case decomp u of
    Left u' -> weaken $ weakenEnd3 u'
    Right t -> inj t

weakenEnd5 :: forall effs a b c d e. Union '[a, b, c, d, e] ~> Union (a ': b ': c ': d ': e ': effs)
weakenEnd5 u = case decomp u of
    Left u' -> weaken $ weakenEnd4 u'
    Right t -> inj t

weakenEnd6 :: forall effs a b c d e f. Union '[a, b, c, d, e, f] ~> Union (a ': b ': c ': d ': e ': f ': effs)
weakenEnd6 u = case decomp u of
    Left u' -> weaken $ weakenEnd5 u'
    Right t -> inj t

weakenEnd7 :: forall effs a b c d e f g. Union '[a, b, c, d, e, f, g] ~> Union (a ': b ': c ': d ': e ': f ': g ': effs)
weakenEnd7 u = case decomp u of
    Left u' -> weaken $ weakenEnd6 u'
    Right t -> inj t

weakenEnd8 :: forall effs a b c d e f g h. Union '[a, b, c, d, e, f, g, h] ~> Union (a ': b ': c ': d ': e ': f ': g ': h ': effs)
weakenEnd8 u = case decomp u of
    Left u' -> weaken $ weakenEnd7 u'
    Right t -> inj t

weakenUnder :: forall effs a b . Union (a ': effs) ~> Union (a ': b ': effs)
weakenUnder u = case decomp u of
    Left u' -> weaken $ weaken u'
    Right t -> inj t

weakenUnderN :: forall effs' effs a . Weakens effs' => Union (a ': effs) ~> Union (a ': (effs' :++: effs))
weakenUnderN u = case decomp u of
    Left u' -> weaken $ weakens @effs' @effs u'
    Right t -> inj t

raiseEnd :: forall effs a . Eff '[a] ~> Eff (a ': effs)
raiseEnd = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd u) (tsingleton $ qComp q loop)

raiseEnd2 :: forall effs a b . Eff '[a, b] ~> Eff (a ': b ': effs)
raiseEnd2 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd2 u) (tsingleton $ qComp q loop)

raiseEnd3 :: forall effs a b c . Eff '[a, b, c] ~> Eff (a ': b ': c ': effs)
raiseEnd3 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd3 u) (tsingleton $ qComp q loop)

raiseEnd4 :: forall effs a b c d. Eff '[a, b, c, d] ~> Eff (a ': b ': c ': d ': effs)
raiseEnd4 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd4 u) (tsingleton $ qComp q loop)

raiseEnd5 :: forall effs a b c d e. Eff '[a, b, c, d, e] ~> Eff (a ': b ': c ': d ': e ': effs)
raiseEnd5 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd5 u) (tsingleton $ qComp q loop)

raiseEnd6 :: forall effs a b c d e f. Eff '[a, b, c, d, e, f] ~> Eff (a ': b ': c ': d ': e ': f ': effs)
raiseEnd6 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd6 u) (tsingleton $ qComp q loop)

raiseEnd7 :: forall effs a b c d e f g. Eff '[a, b, c, d, e, f, g] ~> Eff (a ': b ': c ': d ': e ': f ': g ': effs)
raiseEnd7 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd7 u) (tsingleton $ qComp q loop)

raiseEnd8 :: forall effs a b c d e f g h. Eff '[a, b, c, d, e, f, g, h] ~> Eff (a ': b ': c ': d ': e ': f ': g ': h ': effs)
raiseEnd8 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenEnd8 u) (tsingleton $ qComp q loop)

raiseUnder :: forall effs a b . Eff (a ': effs) ~> Eff (a ': b ': effs)
raiseUnder = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenUnder u) (tsingleton $ qComp q loop)

raiseUnder2 :: forall effs a b c . Eff (a ': effs) ~> Eff (a ': b ': c ': effs)
raiseUnder2 = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenUnder $ weakenUnder u) (tsingleton $ qComp q loop)

raiseUnderN :: forall effs' effs a . Weakens effs' => Eff (a ': effs) ~> Eff (a ': (effs' :++: effs))
raiseUnderN = loop where
    loop = \case
        Val a -> pure a
        E u q -> E (weakenUnderN @effs' @effs @a u) (tsingleton $ qComp q loop)

-- | Handle a 'State' effect in terms of a "larger" 'State' effect from which we have a lens.
handleZoomedState :: Member (State s2) effs => Lens' s2 s1 -> (State s1 ~> Eff effs)
handleZoomedState l = \case
    Get -> view l <$> get
    Put v -> modify (set l v)

-- | Handle a 'Writer' effect in terms of a "larger" 'Writer' effect from which we have a prism.
handleZoomedWriter :: Member (Writer s2) effs => Prism' s2 s1 -> (Writer s1 ~> Eff effs)
handleZoomedWriter p = \case
    Tell w -> tell (review p w)

-- | Handle an 'Error' effect in terms of a "larger" 'Error' effect from which we have a prism.
handleZoomedError :: Member (Error s2) effs => Prism' s2 s1 -> (Error s1 ~> Eff effs)
handleZoomedError p = \case
    Error e -> throwError (review p e)

-- | Handle a 'Reader' effect in terms of a "larger" 'Reader' effect from which we have a getter.
handleZoomedReader :: Member (Reader s2) effs => Getter s2 s1 -> (Reader s1 ~> Eff effs)
handleZoomedReader g = \case
    Ask -> view g <$> ask

-- | Handle a 'Writer' effect in terms of a "larger" 'State' effect from which we have a setter.
writeIntoState
    :: (Monoid s1, Member (State s2) effs)
    => Setter' s2 s1
    -> (Writer s1 ~> Eff effs)
writeIntoState s = \case
    Tell w -> modify (\st -> st & s <>~ w)

-- | Handle a 'State' effect in terms of a monadic effect which has a 'MTL.MonadState' instance.
stateToMonadState
    :: (MTL.MonadState s m)
    => (State s ~> m)
stateToMonadState = \case
    Get -> MTL.get
    Put v -> MTL.put v

monadStateToState
    :: (Member (State s) effs)
    => MTL.State s a
    -> Eff effs a
monadStateToState a = do
    s1 <- get
    let (r, s2) = MTL.runState a s1
    put s2
    return r

-- | Handle an 'Error' effect in terms of a monadic effect which has a 'MTL.MonadError' instance.
errorToMonadError
    :: (MTL.MonadError e m)
    => (Error e ~> m)
errorToMonadError = \case
    Error e -> MTL.throwError e
