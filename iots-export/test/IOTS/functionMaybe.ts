import * as t from 'io-ts';

// IOTSSpec.Slot
const Slot = t.type({
    getSlot: t.Int
});

const MaybeFunctionArgA = t.union([
    Slot,
    t.null
]);

const MaybeFunctionArgReturn = t.string;

type MaybeFunction = (
    a: t.TypeOf<typeof MaybeFunctionArgA>
) => t.TypeOf<typeof MaybeFunctionArgReturn>;
