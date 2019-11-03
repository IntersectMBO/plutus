// IOTSSpec.User
const User = t.type({
    userId: t.number,
    name: t.string
});

const ListFunctionArgs = t.type({
    a: t.array(
        User
    )
});

const ListFunctionReturn = t.string;

export const ListFunction = createEndpoint<typeof ListFunctionArgs, typeof ListFunctionReturn, t.NullC>(
    'ListFunction',
    ListFunctionArgs,
    ListFunctionReturn
);