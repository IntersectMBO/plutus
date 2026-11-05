# multiIndexArray-18: 1025 valid indices fail the count limit

Calls `multiIndexArray` on `[42]` with 1,025 zero indices. Evaluation fails
because the index count exceeds 1,024, even though every index is in bounds.
