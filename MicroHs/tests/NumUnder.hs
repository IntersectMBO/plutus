module NumUnder where

main :: IO ()
main = do
  print 1_000_000
  print 1__000000

  print 0.062_5
  print 0.062__5

  print 3_0e1
  print 3__0e1
  print 4_e+1
  print 4__e+1
  print 4e+0_1
  print 4e+0__1
  print 5_e-1
  print 5__e-1
  print 5e-0_1
  print 5e-0__1
  print 6_e1
  print 6__e1
  print 6e0_1
  print 6e0__1

  print 7_7.2_5
  print 7__7.2__5

  print 8_0.2_5_e0_1
  print 8__0.2__5e0__1

  print 0xffff
  print 0xff_ff
  print 0xff__ff
  print 0x_ffff
  print 0x__ffff
