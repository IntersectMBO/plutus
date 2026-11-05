# multiIndexArray-16: An invalid index between valid lookups fails the whole call

Array argument: `(con (array integer) [10, 20, 30, 40, 50])`.

Index argument: `(con (list integer) [0, 5, 1])`.

Expected result: `evaluation failure`. A valid lookup before the invalid index
must not produce a partial result.
