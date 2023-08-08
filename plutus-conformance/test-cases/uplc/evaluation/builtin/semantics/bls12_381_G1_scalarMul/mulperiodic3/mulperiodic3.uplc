-- Scalar multiplication should be periodic modulo the group size
(program
 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    [
     (builtin bls12_381_G1_scalarMul)
     [
      [ (builtin addInteger) (con integer 123) ]
      [
       [ (builtin multiplyInteger) (con integer 987654321) ]
       (con integer 52435875175126190479447740508185965837690552500527637822603658699938581184513)
      ]
     ]
    ]
   (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
   ]
  ]
  [
   [ (builtin bls12_381_G1_scalarMul) (con integer 123) ]
   (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
  ]
 ]
)

