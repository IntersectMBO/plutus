{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, MagicHash,
             UnliftedFFITypes
  #-}
module Data.JSString.RealFloat ( FPFormat(..)
                               , realFloat
                               , formatRealFloat
                               , formatDouble
                               , formatFloat
                               ) where

import GHC.Exts (Int#, Float#, Double#, Int(..), Float(..), Double(..))

import Data.JSString

-- | Control the rendering of floating point numbers.
data FPFormat = Exponent
              -- ^ Scientific notation (e.g. @2.3e123@).
              | Fixed
              -- ^ Standard decimal notation.
              | Generic
              -- ^ Use decimal notation for values between @0.1@ and
              -- @9,999,999@, and scientific notation otherwise.
                deriving (Enum, Read, Show)

realFloat :: (RealFloat a) => a -> JSString
realFloat = error "Data.JSString.RealFloat.realFloat not yet implemented"
{-# RULES "realFloat/Double" realFloat = genericDouble #-}
{-# RULES "realFoat/Float"   realFloat = genericFloat  #-}
{-# SPECIALIZE realFloat :: Double -> JSString #-}
{-# SPECIALIZE realFloat :: Float -> JSString #-}
{-# NOINLINE realFloat #-}

formatRealFloat :: (RealFloat a)
                => FPFormat
                -> Maybe Int
                -> a
                -> JSString
formatRealFloat = error "Data.JSString.RealFloat.formatRealFloat not yet implemented"
{-# RULES "formatRealFloat/Double" formatRealFloat = formatDouble #-}
{-# RULES "formatRealFloat/Float"  formatRealFloat = formatFloat  #-}
{-# SPECIALIZE formatRealFloat :: FPFormat -> Maybe Int -> Double -> JSString #-}
{-# SPECIALIZE formatRealFloat :: FPFormat -> Maybe Int -> Float -> JSString #-}
{-# NOINLINE formatRealFloat #-}

genericDouble :: Double -> JSString
genericDouble (D# d) = js_doubleGeneric -1# d
{-# INLINE genericDouble #-}

genericFloat :: Float -> JSString
genericFloat (F# f) = js_floatGeneric -1# f
{-# INLINE genericFloat #-}

formatDouble :: FPFormat -> Maybe Int -> Double -> JSString
formatDouble fmt Nothing (D# d)
  = case fmt of
     Fixed    -> js_doubleToFixed -1# d
     Exponent -> js_doubleToExponent -1# d
     Generic  -> js_doubleGeneric -1# d
formatDouble fmt (Just (I# decs)) (D# d)
  = case fmt of
      Fixed    -> js_doubleToFixed decs d
      Exponent -> js_doubleToExponent decs d
      Generic  -> js_doubleGeneric decs d
{-# INLINE formatDouble #-}

formatFloat :: FPFormat -> Maybe Int -> Float -> JSString
formatFloat fmt Nothing (F# f)
  = case fmt of
     Fixed    -> js_floatToFixed -1# f
     Exponent -> js_floatToExponent -1# f
     Generic  -> js_floatGeneric -1# f
formatFloat fmt (Just (I# decs)) (F# f)
  = case fmt of
      Fixed    -> js_floatToFixed decs f
      Exponent -> js_floatToExponent decs f
      Generic  -> js_floatGeneric decs f
{-# INLINE formatFloat #-}


foreign import javascript unsafe
  "h$jsstringDoubleToFixed"
  js_doubleToFixed :: Int# -> Double# -> JSString
foreign import javascript unsafe
  "h$jsstringDoubleToFixed"
  js_floatToFixed :: Int# -> Float# -> JSString

foreign import javascript unsafe
  "h$jsstringDoubleToExponent($1,$2)"
  js_doubleToExponent :: Int# -> Double# -> JSString
foreign import javascript unsafe
  "h$jsstringDoubleToExponent($1,$2)"
  js_floatToExponent :: Int# -> Float# -> JSString
foreign import javascript unsafe
  "h$jsstringDoubleGeneric($1,$2)"
  js_doubleGeneric :: Int# -> Double# -> JSString
foreign import javascript unsafe
  "h$jsstringDoubleGeneric($1,$2)"
  js_floatGeneric :: Int# -> Float# -> JSString
                        
