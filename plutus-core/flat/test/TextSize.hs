{-# LANGUAGE CPP               #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
import Data.Text
import Data.Text.Internal qualified as TI
import PlutusCore.Flat
import PlutusCore.Flat.Encoder.Size
import PlutusCore.Flat.Instances.Text

main = do
#if MIN_VERSION_text(2,0,0)
    print "Text 2 - UTF8"
#else
    print "Text 1 - UTF16"
#endif
    -- UTF-8 1 byte UTF-16 1 unit (2 bytes)
    info "a"

    -- UTF-8 3 bytes UTF-16 1 unit (2 bytes)
    info "是"

    -- UTF-8 4 bytes UTF-16 2 units (4 bytes)
    info "\x1F600"

info t@(TI.Text _ off len) = do
    print ("OFFSET",off,"LEN",len,"UTF_8 LEN",sUTF8Max t,"UTF_16 LEN",sUTF16Max t)
    --,"FLAT UTF8 BITS",unflat (flat (UTF8Text t)) :: Decoded (SizeOf UTF8Text))
