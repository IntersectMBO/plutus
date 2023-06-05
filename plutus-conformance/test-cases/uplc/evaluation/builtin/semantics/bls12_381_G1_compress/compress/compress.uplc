-- Check that compression of a random point in G1 succeeds and gives the expected result.
(program 1.0.0
 [
  (builtin bls12_381_G1_compress)
  (con  bls12_381_G1_element 0x950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)
 ]
)