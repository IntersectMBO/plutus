// IOTSSpec.User
const User = t.type({
    userId: t.number,
    name: t.string
});

const ListFunctionArgA = t.array(
    User
);

const ListFunctionArgReturn = t.string;

type ListFunction = (
    a: t.TypeOf<typeof ListFunctionArgA>
) => t.TypeOf<typeof ListFunctionArgReturn>;
