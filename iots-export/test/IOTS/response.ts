// IOTSSpec.Response
const ResponseString = t.union([
    t.type({"UnknownError": t.tuple([
        t.number,
        t.string
    ])}),
    t.type({"StatusError": t.type({
        code: t.number,
        message: t.string,
        headers: t.record(
            t.string,
            t.number
        )
    })}),
    t.literal('EmptyResponse'),
    t.type({"Response": t.string})
]);