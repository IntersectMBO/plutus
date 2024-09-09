-- Check that indices don't wrap around
(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e4415020567ba2d7d6581b55625553af3)
   ]
   (con (list integer) [-9223372036854775808])  -- minBound :: Int
  ]
  (con (list bool) [True])
 ]
)
