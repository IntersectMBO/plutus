import * as t from 'io-ts'

// Schema.IOTSSpec.Slot
const Slot = t.type({
    getSlot: t.Int
});

class Type {
    constructor(
        readonly someFunction: (
            a: t.union([
                Slot,
                t.null
            ])
        ) => t.string
    ) {}
}
