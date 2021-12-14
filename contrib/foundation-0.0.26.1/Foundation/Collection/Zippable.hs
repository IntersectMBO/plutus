-- |
-- Module      : Foundation.Collection.Zippable
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--
-- Common functions (e. g. 'zip', 'zipWith') that are useful for combining
-- multiple collections.
--
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foundation.Collection.Zippable
    ( BoxedZippable(..)
    , Zippable(..)
    ) where

import qualified Basement.UArray as UV
import qualified Basement.BoxedArray as BA
import qualified Basement.String as S
import           Foundation.Collection.Element
import           Foundation.Collection.Sequential
import           Basement.Compat.Base
import           Basement.Types.AsciiString(AsciiString(..))
import qualified Prelude
import           GHC.ST

class Sequential col => Zippable col where

  -- | 'zipWith' generalises 'zip' by zipping with the function given as the
  --   first argument, instead of a tupling function. For example, @'zipWith' (+)@
  --   is applied to two collections to produce the collection of corresponding
  --   sums.
  zipWith :: (Sequential a, Sequential b)
          => (Element a -> Element b -> Element col)
          -> a -> b -> col
  zipWith f a b = go f (toList a, toList b)
    where go f' = maybe mempty (\(x, xs) -> uncurry2 f' x `cons` go f' xs) . uncons2

  -- | Like 'zipWith', but works with 3 collections.
  zipWith3 :: (Sequential a, Sequential b, Sequential c)
           => (Element a -> Element b -> Element c -> Element col)
           -> a -> b -> c -> col
  zipWith3 f a b c = go f (toList a, toList b, toList c)
    where go f' = maybe mempty (\(x, xs) -> uncurry3 f' x `cons` go f' xs) . uncons3

  -- | Like 'zipWith', but works with 4 collections.
  zipWith4 :: (Sequential a, Sequential b, Sequential c, Sequential d)
           => (Element a -> Element b -> Element c -> Element d -> Element col)
           -> a -> b -> c -> d -> col
  zipWith4 fn a b c d = go fn (toList a, toList b, toList c, toList d)
    where go f' = maybe mempty (\(x, xs) -> uncurry4 f' x `cons` go f' xs) . uncons4

  -- | Like 'zipWith', but works with 5 collections.
  zipWith5 :: (Sequential a, Sequential b, Sequential c, Sequential d, Sequential e)
           => (Element a -> Element b -> Element c -> Element d -> Element e -> Element col)
           -> a -> b -> c -> d -> e -> col
  zipWith5 fn a b c d e = go fn (toList a, toList b, toList c, toList d, toList e)
    where go f' = maybe mempty (\(x, xs) -> uncurry5 f' x `cons` go f' xs) . uncons5

  -- | Like 'zipWith', but works with 6 collections.
  zipWith6 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
              , Sequential f)
           => (Element a -> Element b -> Element c -> Element d -> Element e -> Element f -> Element col)
           -> a -> b -> c -> d -> e -> f -> col
  zipWith6 fn a b c d e f = go fn (toList a, toList b, toList c, toList d, toList e, toList f)
    where go f' = maybe mempty (\(x, xs) -> uncurry6 f' x `cons` go f' xs) . uncons6

  -- | Like 'zipWith', but works with 7 collections.
  zipWith7 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
              , Sequential f, Sequential g )
           => (Element a -> Element b -> Element c -> Element d -> Element e -> Element f -> Element g -> Element col)
           -> a -> b -> c -> d -> e -> f -> g -> col
  zipWith7 fn a b c d e f g = go fn (toList a, toList b, toList c, toList d, toList e, toList f, toList g)
    where go f' = maybe mempty (\(x, xs) -> uncurry7 f' x `cons` go f' xs) . uncons7

instance Zippable [c]

instance UV.PrimType ty => Zippable (UV.UArray ty) where
  zipWith f as bs = runST $ UV.builderBuild_ 64 $ go f (toList as) (toList bs)
    where
      go _  []       _        = return ()
      go _  _        []       = return ()
      go f' (a':as') (b':bs') = UV.builderAppend (f' a' b') >> go f' as' bs'

instance Zippable (BA.Array ty) where
  zipWith f as bs = runST $ BA.builderBuild_ 64 $ go f (toList as) (toList bs)
    where
      go _  []       _        = return ()
      go _  _        []       = return ()
      go f' (a':as') (b':bs') = BA.builderAppend (f' a' b') >> go f' as' bs'

instance Zippable S.String where
  zipWith f as bs = runST $ S.builderBuild_ 64 $ go f (toList as) (toList bs)
    where
      go _  []       _        = return ()
      go _  _        []       = return ()
      go f' (a':as') (b':bs') = S.builderAppend (f' a' b') >> go f' as' bs'

deriving instance Zippable AsciiString

class Zippable col => BoxedZippable col where

  -- | 'zip' takes two collections and returns a collections of corresponding
  --   pairs. If one input collection is short, excess elements of the longer
  --   collection are discarded.
  zip :: ( Sequential a, Sequential b
         , Element col ~ (Element a, Element b) )
      => a -> b -> col
  zip = zipWith (,)

  -- | Like 'zip', but works with 3 collections.
  zip3 :: ( Sequential a, Sequential b, Sequential c
          , Element col ~ (Element a, Element b, Element c) )
       => a -> b -> c -> col
  zip3 = zipWith3 (,,)

  -- | Like 'zip', but works with 4 collections.
  zip4 :: ( Sequential a, Sequential b, Sequential c, Sequential d
          , Element col ~ (Element a, Element b, Element c, Element d) )
       => a -> b -> c -> d -> col
  zip4 = zipWith4 (,,,)

  -- | Like 'zip', but works with 5 collections.
  zip5 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
          , Element col ~ (Element a, Element b, Element c, Element d, Element e) )
       => a -> b -> c -> d -> e -> col
  zip5 = zipWith5 (,,,,)

  -- | Like 'zip', but works with 6 collections.
  zip6 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e, Sequential f
          , Element col ~ (Element a, Element b, Element c, Element d, Element e, Element f) )
       => a -> b -> c -> d -> e -> f -> col
  zip6 = zipWith6 (,,,,,)

  -- | Like 'zip', but works with 7 collections.
  zip7 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e, Sequential f, Sequential g
          , Element col ~ (Element a, Element b, Element c, Element d, Element e, Element f, Element g) )
       => a -> b -> c -> d -> e -> f -> g -> col
  zip7 = zipWith7 (,,,,,,)

  -- | 'unzip' transforms a collection of pairs into a collection of first
  --   components and a collection of second components.
  unzip :: (Sequential a, Sequential b, Element col ~ (Element a, Element b))
        => col -> (a, b)
  unzip = go . toList
    where go []          = (mempty, mempty)
          go ((a, b):xs) =
              let (as, bs) = go xs
              in (a `cons` as, b `cons` bs)

  -- | Like 'unzip', but works on a collection of 3-element tuples.
  unzip3 :: ( Sequential a, Sequential b, Sequential c
            , Element col ~ (Element a, Element b, Element c) )
         => col -> (a, b, c)
  unzip3 = go . toList
    where go [] = (mempty, mempty, mempty)
          go ((a, b, c):xs) =
              let (as, bs, cs) = go xs
              in (a `cons` as, b `cons` bs, c `cons` cs)

  -- | Like 'unzip', but works on a collection of 4-element tuples.
  unzip4 :: ( Sequential a, Sequential b, Sequential c, Sequential d
            , Element col ~ (Element a, Element b, Element c, Element d) )
         => col -> (a, b, c, d)
  unzip4 = go . toList
    where go [] = (mempty, mempty, mempty, mempty)
          go ((a, b, c, d):xs) =
              let (as, bs, cs, ds) = go xs
              in (a `cons` as, b `cons` bs, c `cons` cs, d `cons` ds)

  -- | Like 'unzip', but works on a collection of 5-element tuples.
  unzip5 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
            , Element col ~ (Element a, Element b, Element c, Element d, Element e) )
         => col -> (a, b, c, d, e)
  unzip5 = go . toList
    where go [] = (mempty, mempty, mempty, mempty, mempty)
          go ((a, b, c, d, e):xs) =
              let (as, bs, cs, ds, es) = go xs
              in (a `cons` as, b `cons` bs, c `cons` cs, d `cons` ds, e `cons` es)

  -- | Like 'unzip', but works on a collection of 6-element tuples.
  unzip6 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e, Sequential f
            , Element col ~ (Element a, Element b, Element c, Element d, Element e, Element f) )
         => col -> (a, b, c, d, e, f)
  unzip6 = go . toList
    where go [] = (mempty, mempty, mempty, mempty, mempty, mempty)
          go ((a, b, c, d, e, f):xs) =
              let (as, bs, cs, ds, es, fs) = go xs
              in (a `cons` as, b `cons` bs, c `cons` cs, d `cons` ds, e `cons` es, f `cons` fs)

  -- | Like 'unzip', but works on a collection of 7-element tuples.
  unzip7 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e, Sequential f, Sequential g
            , Element col ~ (Element a, Element b, Element c, Element d, Element e, Element f, Element g) )
        => col -> (a, b, c, d, e, f, g)
  unzip7 = go . toList
    where go [] = (mempty, mempty, mempty, mempty, mempty, mempty, mempty)
          go ((a, b, c, d, e, f, g):xs) =
              let (as, bs, cs, ds, es, fs, gs) = go xs
              in (a `cons` as, b `cons` bs, c `cons` cs, d `cons` ds, e `cons` es, f `cons` fs, g `cons` gs)

instance BoxedZippable [a]
instance BoxedZippable (BA.Array ty)


-- * Tuple helper functions

uncons2 :: (Sequential a, Sequential b) => (a, b) -> Maybe ((Element a, Element b), (a, b))
uncons2 xs = let (as, bs) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   return ((a', b'), (as', bs'))

uncons3 :: (Sequential a, Sequential b, Sequential c)
        => (a, b, c)
        -> Maybe ((Element a, Element b, Element c), (a, b, c))
uncons3 xs = let (as, bs, cs) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   (c', cs') <- uncons cs
                   return ((a', b', c'), (as', bs', cs'))

uncons4 :: (Sequential a, Sequential b, Sequential c, Sequential d)
        => (a, b, c, d)
        -> Maybe ( (Element a, Element b, Element c, Element d)
                 , (a, b, c, d) )
uncons4 xs = let (as, bs, cs, ds) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   (c', cs') <- uncons cs
                   (d', ds') <- uncons ds
                   return ((a', b', c', d'), (as', bs', cs', ds'))

uncons5 :: (Sequential a, Sequential b, Sequential c, Sequential d, Sequential e)
        => (a, b, c, d, e)
        -> Maybe ( (Element a, Element b, Element c, Element d, Element e)
                 , (a, b, c, d, e) )
uncons5 xs = let (as, bs, cs, ds, es) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   (c', cs') <- uncons cs
                   (d', ds') <- uncons ds
                   (e', es') <- uncons es
                   return ((a', b', c', d', e'), (as', bs', cs', ds', es'))

uncons6 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
           , Sequential f )
        => (a, b, c, d, e, f)
        -> Maybe ( (Element a, Element b, Element c, Element d, Element e, Element f)
                 , (a, b, c, d, e, f) )
uncons6 xs = let (as, bs, cs, ds, es, fs) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   (c', cs') <- uncons cs
                   (d', ds') <- uncons ds
                   (e', es') <- uncons es
                   (f', fs') <- uncons fs
                   return ((a', b', c', d', e', f'), (as', bs', cs', ds', es', fs'))

uncons7 :: ( Sequential a, Sequential b, Sequential c, Sequential d, Sequential e
           , Sequential f, Sequential g )
        => (a, b, c, d, e, f, g)
        -> Maybe ( (Element a, Element b, Element c, Element d, Element e, Element f
                 , Element g)
                 , (a, b, c, d, e, f, g) )
uncons7 xs = let (as, bs, cs, ds, es, fs, gs) = xs
             in do (a', as') <- uncons as
                   (b', bs') <- uncons bs
                   (c', cs') <- uncons cs
                   (d', ds') <- uncons ds
                   (e', es') <- uncons es
                   (f', fs') <- uncons fs
                   (g', gs') <- uncons gs
                   return ( (a', b', c', d', e', f', g')
                          , (as', bs', cs', ds', es', fs', gs') )

uncurry2 :: (a -> b -> c) -> (a, b) -> c
uncurry2 = Prelude.uncurry

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 fn (a, b, c) = fn a b c

uncurry4 :: (a -> b -> c -> d -> g) -> (a, b, c, d) -> g
uncurry4 fn (a, b, c, d) = fn a b c d

uncurry5 :: (a -> b -> c -> d -> e -> f) -> (a, b, c, d, e) -> f
uncurry5 fn (a, b, c, d, e) = fn a b c d e

uncurry6 :: (a -> b -> c -> d -> e -> f -> g) -> (a, b, c, d, e, f) -> g
uncurry6 fn (a, b, c, d, e, f) = fn a b c d e f

uncurry7 :: (a -> b -> c -> d -> e -> f -> g -> h) -> (a, b, c, d, e, f, g) -> h
uncurry7 fn (a, b, c, d, e, f, g) = fn a b c d e f g
