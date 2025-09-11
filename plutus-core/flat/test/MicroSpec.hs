import Data.ByteString qualified as B
import Data.List
import PlutusCore.Flat
import Test.E
import Test.E.Flat
import Test.Microspec

-- t = (size E256_256 0, flat E256_4)

main :: IO ()
main = microspec $ do
      valTest E3_1   1 [1]
      valTest E3_3   2 [193]
      valTest E16_1  4 [1]
      valTest E16_16 4 [241]

      --valTest E256_1   8 [0, 1]
      --valTest E256_256 8 [255, 1]

      -- describe "reverse" $ do
      --       it "reverse . reverse === id"
      --             $ \l -> reverse (reverse l) === (l :: [Int])

      -- describe "tail" $ it "length is -1" $ \(NonEmpty l) ->
      --       length (tail l :: [Int]) === length l - 1

      -- describe "solve the halting problem" $ pending

valTest v sz enc = describe (show v) $ do
      it "has right size" $ size v 0 === sz
      it "has right encoding" $ B.unpack (flat v) === enc
