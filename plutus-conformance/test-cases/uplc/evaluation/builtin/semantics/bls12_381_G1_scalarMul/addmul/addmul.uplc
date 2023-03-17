-- 2157p + 2157q for random points p and q in G1.  This should give the same result as muladd.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_add)
   [
    [
     (builtin bls12_381_G1_scalarMul)
     (con integer 2157)
    ]
    (con bls12_381_G1_element 0x950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)
   ]
  ]
  [
   [
    (builtin bls12_381_G1_scalarMul)
    (con integer 2157)
   ]
   (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
  ]
 ]
)