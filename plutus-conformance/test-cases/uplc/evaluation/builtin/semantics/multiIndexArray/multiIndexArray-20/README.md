# multiIndexArray-20: Bytestring elements retain their values, order and duplicates

Array argument: `(con (array bytestring) [#00, #ff01])`.

Index argument: `(con (list integer) [1, 0, 1])`.

Expected result: `(con (list bytestring) [#ff01, #00, #ff01])`.
