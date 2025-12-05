#!/bin/bash
cat "$*" |
    sed 's#/# #g' |
    sed 's/,/ /g' |
    #    grep -v "^Nop" |
    grep -v "^#" |
    awk '
      BEGIN {printf ("name x     y      z      u      v      w      t      lb     ub\n")}
      function print1() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2,  0,  0,  0,  0,  0, $3, $4,  $5)}
      function print2() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2, $3,  0,  0,  0,  0, $4, $5,  $6)}
      function print3() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2, $3, $4,  0,  0,  0, $5, $6,  $7)}
      function print4() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2, $3, $4, $5,  0,  0, $6, $7,  $8)}
      function print5() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2, $3, $4, $5, $6,  0, $7, $8,  $9)}
      function print6() {printf ("%-20s %7d %7d %7d %7d %7d %7d  %g %g %g \n", $1, $2, $3, $4, $5, $6, $7, $8, $9, $10)}
      NF == 8  {print1()}
      NF == 9  {print2()}
      NF == 10 {print3()}
      NF == 11 {print4()}
      NF == 12 {print5()}
      NF == 13 {print6()}
    '   
