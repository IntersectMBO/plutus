# policies-06: More than 256 policies

Enumerate 257 distinct policies (#0000 through #0100). The filter-list limit does not bound the size of a Value.

Value argument (abbreviated): `(con value [ (#0000, [(#, 1)]), (#0001, [(#, 1)]), ..., (#0100, [(#, 1)]) ])`.

257 policies, `#0000` through `#0100` inclusive, each containing the empty token name with quantity 1.

`...` abbreviates the entries described above. The full constants are in [policies-06.uplc](policies-06.uplc).

Expected result: the 257 policy IDs #0000 through #0100, in ascending byte order.
