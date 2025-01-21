-- Scalar multiplication should be periodic modulo the group size
(program
 1.0.0
 [
  [
   (builtin bls12_381_G2_equal)
   [
    [
     (builtin bls12_381_G2_scalarMul)
     [
      [ (builtin addInteger) (con integer 123) ]
      (con integer 52435875175126190479447740508185965837690552500527637822603658699938581184513)
     ]
    ]
    (con bls12_381_G2_element
     0xb0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1)
   ]
  ]
  [
   [ (builtin bls12_381_G2_scalarMul) (con integer 123) ]
   (con bls12_381_G2_element
    0xb0629fa1158c2d23a10413fe91d381a84d25e31d041cd0377d25828498fd02011b35893938ced97535395e4815201e67108bcd4665e0db25d602d76fa791fab706c54abf5e1a9e44b4ac1e6badf3d2ac0328f5e30be341677c8bac5dda7682f1)
  ]
 ]
)

