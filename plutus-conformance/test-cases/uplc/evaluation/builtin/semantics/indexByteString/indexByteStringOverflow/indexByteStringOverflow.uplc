-- this is different than out-of-bounds error, the index argument overflow'ed the maxBound :: Int64
-- same error would happen when underflow'ing the minBound :: Int64
(program 1.0.0 [(builtin indexByteString) (con bytestring #00) (con integer 9223372036854775808)])