-- Check that a particular integer encodes to the expected bytestring with some
-- extra padding on the right when the width is greater than the minimal
-- required width.
(program 1.0.0
 [(builtin integerToByteString) (con bool False) (con integer 12) (con integer 20016001699311)]
)
