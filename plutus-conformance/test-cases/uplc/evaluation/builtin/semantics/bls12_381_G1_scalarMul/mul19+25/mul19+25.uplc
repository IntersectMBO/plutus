-- 19p+25p for a random point p in G1.  This should give the same result as mul44.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_add)
   [
    [
     (builtin bls12_381_G1_scalarMul)
     (con integer 19)
    ]
    (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
   ]
  ]
  [
   [
    (builtin bls12_381_G1_scalarMul)
    (con integer 25)
   ]
   (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
  ]
 ]
)
