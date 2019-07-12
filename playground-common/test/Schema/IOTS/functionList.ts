import * as t from 'io-ts'

// Schema.IOTSSpec.User
const User = t.type({
    userId: t.Int,
    name: t.string,
    children: t.array(User)
});

class Type {
    constructor(
        readonly someFunction: (
            a: t.array(User)
        ) => t.string
    ) {}
}
