import * as t from 'io-ts';

// IOTSSpec.User
const User = t.type({
    userId: t.Int,
    name: t.string
});
