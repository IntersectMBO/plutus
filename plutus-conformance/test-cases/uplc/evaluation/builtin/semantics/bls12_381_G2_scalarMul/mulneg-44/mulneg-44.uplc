-- Multiplying a random point in G2 by the scalar -44 gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G2_scalarMul)
   (con integer -44)
  ]
  (con bls12_381_G2_element 0x8310bc97fc7ad9b1616e51226c6a521b9d7fdf03f7299833e6a208ae0399fec76045a43ceef846e0958d0cdf05cf2b1f00460ee6edd2778b413eb7c272bc5b94d12b910f8ac4eb1b55e50a93644714787417bc462349c5e0f6f357b9ac32262a)
 ]
)
