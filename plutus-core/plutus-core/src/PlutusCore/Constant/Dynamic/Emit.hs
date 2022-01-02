module PlutusCore.Constant.Dynamic.Emit
    ( Emitter (..)
    , runEmitter
    , emit
    ) where

import Control.Monad.Writer.Strict
import Data.DList as DList
import Data.Text (Text)

newtype Emitter a = Emitter
    { unEmitter :: Writer (DList Text) a
    } deriving newtype (Functor, Applicative, Monad)

runEmitter :: Emitter a -> (a, DList Text)
runEmitter = runWriter . unEmitter

emit :: Text -> Emitter ()
emit text = Emitter . tell $ pure text
