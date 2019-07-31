import * as t from 'io-ts';

// IOTSSpec.Response
const ResponseString = t.union([
    t.type({"UnknownError": t.tuple([
        t.Int,
        t.string
    ])}),
    t.type({"StatusError": t.type({
        code: t.Int,
        message: t.string,
        headers: t.record(
            t.string,
            t.Int
        )
    })}),
    t.literal('EmptyResponse'),
    t.type({"Response": t.string})
]);
