module PlutusCore.Crypto.BLS12_381.Error
where

data BLS12_381_Error
  = HashToCurveDstTooBig -- DSTs can be at most 255 bytes long.
  deriving stock (Show)
