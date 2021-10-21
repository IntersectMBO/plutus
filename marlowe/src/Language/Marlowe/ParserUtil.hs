module Language.Marlowe.ParserUtil where

import qualified Data.Aeson       as JSON
import           Data.Aeson.Types hiding (Error, Value)
import           Data.Scientific  (Scientific, floatingOrInteger)

getInteger :: Scientific -> Parser Integer
getInteger x = case (floatingOrInteger x :: Either Double Integer) of
                 Right a -> return a
                 Left _  -> fail "Account number is not an integer"

withInteger :: JSON.Value -> Parser Integer
withInteger = withScientific "" getInteger

customOptions :: Options
customOptions = defaultOptions
                { unwrapUnaryRecords = True
                , sumEncoding = TaggedObject { tagFieldName = "tag", contentsFieldName = "contents" }
                }
