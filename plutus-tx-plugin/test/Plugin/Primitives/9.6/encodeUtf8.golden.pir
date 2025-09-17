let
  !encodeUtf : string -> bytestring = encodeUtf8
  ~encodeUtf : string -> bytestring = encodeUtf
in
encodeUtf "abc"