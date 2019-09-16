// Ledger.Slot.Slot
const Slot = t.type({
    getSlot: t.number
});

// Ledger.Value.CurrencySymbol
const CurrencySymbol = t.type({
    unCurrencySymbol: t.string
});

// Ledger.Value.TokenName
const TokenName = t.type({
    unTokenName: t.string
});

// Language.PlutusTx.AssocMap.Map
const MapTokenNameInteger = t.type({
    unMap: t.array(
        t.tuple([
            TokenName,
            t.number
        ])
    )
});

// Language.PlutusTx.AssocMap.Map
const MapCurrencySymbolMapTokenNameInteger = t.type({
    unMap: t.array(
        t.tuple([
            CurrencySymbol,
            MapTokenNameInteger
        ])
    )
});

// Ledger.Value.Value
const Value = t.type({
    getValue: MapCurrencySymbolMapTokenNameInteger
});

// Wallet.Emulator.Types.Wallet
const Wallet = t.type({
    getWallet: t.number
});

const ScheduleCollectionArgA = Slot;

const ScheduleCollectionArgB = Value;

const ScheduleCollectionArgC = Slot;

const ScheduleCollectionArgD = Wallet;

const ScheduleCollectionArgReturn = t.null;

type ScheduleCollection = (
    a: t.TypeOf<typeof ScheduleCollectionArgA>,
    b: t.TypeOf<typeof ScheduleCollectionArgB>,
    c: t.TypeOf<typeof ScheduleCollectionArgC>,
    d: t.TypeOf<typeof ScheduleCollectionArgD>
) => t.TypeOf<typeof ScheduleCollectionArgReturn>;

const ContributeArgA = Slot;

const ContributeArgB = Value;

const ContributeArgC = Slot;

const ContributeArgD = Wallet;

const ContributeArgE = Value;

const ContributeArgReturn = t.null;

type Contribute = (
    a: t.TypeOf<typeof ContributeArgA>,
    b: t.TypeOf<typeof ContributeArgB>,
    c: t.TypeOf<typeof ContributeArgC>,
    d: t.TypeOf<typeof ContributeArgD>,
    e: t.TypeOf<typeof ContributeArgE>
) => t.TypeOf<typeof ContributeArgReturn>;
