-- Later updates to duplicate indices take precedence.
(program 1.0.0
 [
  [
   (builtin writeBits)
   [
    [
     [
      (builtin writeBits)
      (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
     ]
     (con (list integer) [340, 342, 343, 340, 342, 343])
    ]
    (con bool True)
   ]
   (con (list integer) [340, 342, 343])
  ]
  (con bool False)
 ]
)