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
     (con (list integer) [340, 342, 344])  -- 344 is out of bounds
    ]
    (con bool True)
   ]
   (con (list integer) [344, 340, 342, 343])
  ]
  (con bool False)
 ]
)