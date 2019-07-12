import * as t from 'io-ts'

// Schema.IOTSSpec.SimpleSum
const SimpleSum = t.union([
    t.literal('This'),
    t.literal('That'),
    t.literal('TheOther')
]);
