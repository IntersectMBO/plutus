module MString where {

s1 :: String;
s1 =
"""
Line 1
Line 2
Line 3
"""
;
r1 :: String;
r1 =
   "Line 1\n"
++ "Line 2\n"
++ "Line 3"
;

s2 :: String;
s2 =
"""Test
Line 1
Line 2
Line 3
"""
;
r2 :: String;
r2 =
   "Test\n"
++ "Line 1\n"
++ "Line 2\n"
++ "Line 3";

s3 :: String;
s3 =
"""
"Hello"
\"\"\"
\"""
""";
r3 :: String;
r3 =
   "\"Hello\"\n"
++ "\"\"\"\n"
++ "\"\"\"";

s4 :: String;
s4 =
"""
  <div>
    <p>ABC</p>
  </div>
""";
r4 :: String;
r4 =
   "<div>\n"
++ "  <p>ABC</p>\n"
++ "</div>";

s5 :: String;
s5 =
"""
  \&  Line 1
  \&  Line 2
  \&  Line 3
""";
r5 :: String;
r5 =
   "  Line 1\n"
++ "  Line 2\n"
++ "  Line 3";

s6 :: String;
s6 =
"""
Hello

""";
r6 :: String;
r6 = "Hello\n";

main :: IO ();
main = do {
  print $ s1 == r1;
  print $ s2 == r2;
  print $ s3 == r3;
  print $ s4 == r4;
  print $ s5 == r5;
  print $ s6 == r6;
--  print s1;
--  print r1;
  }
}
