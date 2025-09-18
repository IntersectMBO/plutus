let
  data MyD_1099 | MyD_match_1102 where
    MyD_1100 : integer -> MyD_1099
    MyD_1101 : bytestring -> MyD_1099
in
mkCons {data} (iData 1) (mkNilData ())