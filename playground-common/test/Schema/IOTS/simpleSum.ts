import * as t from 'io-ts'


// Schema.IOTSSpec
const SimpleSum = t.union([
    t.literal('This'),
    t.literal('That')
]);
