{-# LANGUAGE EmptyDataDecls #-}

module JavaScript.Web.Canvas.Internal ( Canvas(..)
                                      , Context(..)
                                      , Gradient(..)
                                      , Image(..)
                                      , ImageData(..)
                                      , Pattern(..)
                                      , TextMetrics(..)
                                      ) where

import GHCJS.Types

newtype Canvas      = Canvas      JSVal
newtype Context     = Context     JSVal
newtype Gradient    = Gradient    JSVal
newtype Image       = Image       JSVal
newtype ImageData   = ImageData   JSVal
newtype Pattern     = Pattern     JSVal
newtype TextMetrics = TextMetrics JSVal

instance IsJSVal Canvas
instance IsJSVal Context
instance IsJSVal Gradient
instance IsJSVal Image
instance IsJSVal ImageData
instance IsJSVal Pattern
instance IsJSVal TextMetrics
