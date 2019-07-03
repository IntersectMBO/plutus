import * as t from 'io-ts'


// Schema.IOTSSpec
const User = t.type({
    userId: t.Int,
    name: t.string
});
