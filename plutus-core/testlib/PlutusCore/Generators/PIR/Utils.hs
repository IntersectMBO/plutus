{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module PlutusCore.Generators.PIR.Utils where


import Data.String
import Prettyprinter
import Test.QuickCheck

import PlutusIR.Core.Instance.Pretty.Readable


-- | Show a `Doc` when a property fails.
ceDoc :: Testable t => Doc ann -> t -> Property
ceDoc d = counterexample (show d)

-- | Bind a value to a name in a property so that
-- it is displayed as a `name = thing` binding if the
-- property fails.
letCE :: (PrettyPir a, Testable p)
      => String
      -> a
      -> (a -> p)
      -> Property
letCE name x k = ceDoc (fromString name <+> "=" <+> prettyPirReadable x) (k x)

-- | Like `forAllShrink` but displays the bound value as
-- a named pretty-printed binding like `letCE`
forAllDoc :: (PrettyPir a, Testable p)
          => String
          -> Gen a
          -> (a -> [a])
          -> (a -> p)
          -> Property
forAllDoc name g shr k =
  forAllShrinkBlind g shr $ \ x ->
    ceDoc (fromString name <+> "=" <+> prettyPirReadable x)
          (k x)

