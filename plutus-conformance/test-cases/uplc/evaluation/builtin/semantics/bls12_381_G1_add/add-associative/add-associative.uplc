-- p+(q+r) = (p+q)+r for three random points on G1.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    [
     (builtin bls12_381_G1_add)
     (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
    ]
    [
     [
      (builtin bls12_381_G1_add)
       (con bls12_381_G1_element 0x950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)
     ]
    (con bls12_381_G1_element 0xb962fd0cc81048e0cf7557bf3e4b6edc5ab4bfb3dc87f83af428b6300727b139c404ab159bdf2eaea3f649903421537f)
   ]
  ]
 ]
  [
   (builtin bls12_381_G1_add)
   [
    [
     (builtin bls12_381_G1_add)
     (con bls12_381_G1_element 0xabd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)
    ]
    (con bls12_381_G1_element 0x950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)
   ]
   (con bls12_381_G1_element 0xb962fd0cc81048e0cf7557bf3e4b6edc5ab4bfb3dc87f83af428b6300727b139c404ab159bdf2eaea3f649903421537f)
  ]
 ]
)

