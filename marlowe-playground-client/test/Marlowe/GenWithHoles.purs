module Marlowe.GenWithHoles where

import Prelude
import Control.Lazy (class Lazy)
import Control.Monad.Gen (class MonadGen, chooseBool, chooseFloat, chooseInt, resize, sized)
import Control.Monad.Reader (class MonadAsk, class MonadReader, ReaderT(..), runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Test.QuickCheck (class Testable)
import Test.QuickCheck.Gen (Gen)
import Test.Unit (Test)
import Test.Unit.QuickCheck (quickCheck)
import Marlowe.Gen (GenerationOptions)

-- TODO: rename to GenContract or similar
newtype GenWithHoles a
  = GenWithHoles (ReaderT GenerationOptions Gen a)

unGenWithHoles :: forall a. GenWithHoles a -> ReaderT GenerationOptions Gen a
unGenWithHoles (GenWithHoles g) = g

derive newtype instance genWithGenWithHolessFunctor :: Functor GenWithHoles

derive newtype instance genWithGenWithHolessApply :: Apply GenWithHoles

derive newtype instance genWithGenWithHolessApplicative :: Applicative GenWithHoles

derive newtype instance genWithGenWithHolessBind :: Bind GenWithHoles

instance genWithGenWithHolessMonad :: Monad GenWithHoles

derive newtype instance genWithGenWithHolessMonadAsk :: MonadAsk GenerationOptions GenWithHoles

derive newtype instance genWithGenWithHolessMonadReader :: MonadReader GenerationOptions GenWithHoles

instance genWithGenWithHolessLazy :: Lazy (GenWithHoles a) where
  defer f = f unit

derive newtype instance genWithGenWithHolessMonadRec :: MonadRec GenWithHoles

instance genWithGenWithHolessMonadGen :: MonadGen GenWithHoles where
  chooseInt from to = GenWithHoles $ ReaderT $ const $ chooseInt from to
  chooseFloat from to = GenWithHoles $ ReaderT $ const $ chooseFloat from to
  chooseBool = GenWithHoles $ ReaderT $ const $ chooseBool
  resize f (GenWithHoles (ReaderT g)) = GenWithHoles $ ReaderT $ \b -> resize f (g b)
  sized f =
    GenWithHoles $ ReaderT
      $ \v ->
          sized
            ( \i ->
                let
                  (GenWithHoles (ReaderT q)) = (f i)
                in
                  q v
            )

contractQuickCheck :: forall prop. Testable prop => GenerationOptions -> GenWithHoles prop -> Test
contractQuickCheck options g = quickCheck $ runReaderT (unGenWithHoles g) options
