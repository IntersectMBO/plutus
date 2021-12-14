var h$crc32table = null;
function h$crc32(crc, ptr_d, ptr_o, len) {
    if(!h$crc32table) {
        h$crc32table = new Uint32Array(256);
        for(var i=256; i--;) {
            var tmp = i;
            for(var k=8; k--;) {
                tmp = tmp & 1 ? 3988292384 ^ tmp >>> 1 : tmp >>> 1;
            }
            h$crc32table[i] = tmp;
        }        
    }

    crc = crc ^ -1;
    for(var i=0; i < len; i++) {
        crc = crc >>> 8 ^ h$crc32table[ crc & 255 ^ ptr_d.u8[ptr_o+i] ];
    }

    return (crc ^ -1);
}
