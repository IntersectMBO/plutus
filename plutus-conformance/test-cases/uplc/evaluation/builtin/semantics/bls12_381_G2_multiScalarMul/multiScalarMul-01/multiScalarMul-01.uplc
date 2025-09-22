-- Multi-scalar multiplication is the same as ordinary scalar multiplication for inputs of size 1.
(program 1.0.0
 [(builtin bls12_381_G2_equal)
  [(builtin bls12_381_G2_multiScalarMul)
   (con (list integer) [-7843724524521392138901923801823923123123454352157])
   (con (list bls12_381_G2_element) [0xae2eee55b1b79df45e4d5530912e0d6631268206308ac456b1ee790be4b3f545cf6a7341c7d81ea8ec587dbde47392c207195fc213a5971aecb26cfa6178eb7c765a48c1fe5baf3da8cd499841754672e6ca5a1e7617cf6aa40fdf6305624127
])
  ]
  [(builtin bls12_381_G2_scalarMul)
   (con integer -7843724524521392138901923801823923123123454352157)
   (con bls12_381_G2_element 0xae2eee55b1b79df45e4d5530912e0d6631268206308ac456b1ee790be4b3f545cf6a7341c7d81ea8ec587dbde47392c207195fc213a5971aecb26cfa6178eb7c765a48c1fe5baf3da8cd499841754672e6ca5a1e7617cf6aa40fdf6305624127)
  ]
 ]
)
