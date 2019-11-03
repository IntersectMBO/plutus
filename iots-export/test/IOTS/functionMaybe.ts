// IOTSSpec.Slot
const Slot = t.type({
    getSlot: t.number
});

const MaybeFunctionArgs = t.type({
    a: t.union([
        Slot,
        t.null
    ])
});

const MaybeFunctionReturn = t.string;

export const MaybeFunction = createEndpoint<typeof MaybeFunctionArgs, typeof MaybeFunctionReturn, t.NullC>(
    'MaybeFunction',
    MaybeFunctionArgs,
    MaybeFunctionReturn
);