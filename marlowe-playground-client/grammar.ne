@{%
const moo = require("moo");

const lexer = moo.compile({
        WS: /[ \t]+/,
        number: /0|-?[1-9][0-9]*/,
        base16: {match: /"(?:[0-9a-fA-F][0-9a-fA-F])*"/, value: x => x.slice(1, -1)},
        string: {match: /"(?:\\["\\]|[^\n"\\])*"/, value: x => x.slice(1, -1)},
        ratio: '%',
        comma: ',',
        lparen: '(',
        rparen: ')',
        lsquare: '[',
        rsquare: ']',
        hole: /\?[a-zA-Z0-9_-]+/,
        CONSTRUCTORS: {
            match: /[A-Z][A-Za-z]+/, type: moo.keywords({
                CONTRACT: ['Close', 'Pay', 'If', 'When', 'Let', 'Assert'],
                OBSERVATION: [
                    'AndObs',
                    'OrObs',
                    'NotObs',
                    'ChoseSomething',
                    'ValueGE',
                    'ValueGT',
                    'ValueLT',
                    'ValueLE',
                    'ValueEQ',
                    'TrueObs',
                    'FalseObs',
                ],
                VALUE: [
                    'AvailableMoney',
                    'Constant',
                    'NegValue',
                    'AddValue',
                    'SubValue',
                    'MulValue',
                    'Scale',
                    'ChoiceValue',
                    'SlotIntervalStart',
                    'SlotIntervalEnd',
                    'UseValue',
                    'Cond'
                ],
                TOKEN: ['Token'],
                PAYEE: ['Account', 'Party'],
                PARTY: ['PK', 'Role'],
                BOUND: ['Bound'],
                VALUE_ID: ['ValueId'],
                CASE: ['Case'],
                ACTION: ['Deposit', 'Choice', 'Notify'],
                CHOICE_ID: ['ChoiceId'],
            })
        },
        NL: { match: /\n/, lineBreaks: true },
        myError: {match: /[\$?`]/, error: true},
});

%}

# Pass your lexer object using the @lexer option:
@lexer lexer

main -> ws:* topContract ws:* {%([,contract,]) => contract%}

ws -> %WS | %NL

# At least one whitespace
someWS -> ws:+

# none or some whitespace
manyWS -> ws:*

lparen -> %lparen  manyWS {% ([t,]) => t %}

rparen ->  manyWS %rparen {% ([,t]) => t %}

lsquare -> %lsquare manyWS

rsquare ->  manyWS %rsquare

hole -> %hole {% ([hole]) => opts.mkHole(hole.value.substring(1))({startLineNumber: hole.line, startColumn: hole.col, endLineNumber: hole.line, endColumn: hole.col + hole.value.length}) %}

number
   -> %number {% ([n]) => opts.mkBigInteger(n.value) %}
    | lparen %number rparen {% ([,n,]) => opts.mkBigInteger(n.value) %}

timeout
   -> %number {% ([n]) => opts.mkTimeout(n.value)({startLineNumber: n.line, startColumn: n.col, endLineNumber: n.line, endColumn: n.col + n.toString(10).length}) %}
    | lparen %number rparen {% ([start,n,end]) => opts.mkTimeout(n.value)({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

string
   -> %string {% ([s]) => s.value %}
    | %base16 {% ([s]) => s.value %}

base16
   -> %base16 {% ([s]) => s.value %}

topContract
   -> hole {% ([hole]) => hole %}
    | "Close" {% ([{line, col}]) => opts.mkTerm(opts.mkClose)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 5}) %}
    | "Pay" someWS party someWS payee someWS token someWS value someWS contract {% ([{line, col},,party,,payee,,token,,value,,contract]) => opts.mkTerm(opts.mkPay(party)(payee)(token)(value)(contract))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract).endLineNumber, endColumn: opts.getRange(contract).endColumn}) %}
    | "If" someWS observation someWS contract someWS contract {% ([{line, col},,observation,,contract1,,contract2]) => opts.mkTerm(opts.mkIf(observation)(contract1)(contract2))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract2).endLineNumber, endColumn: opts.getRange(contract2).endColumn}) %}
    | "When" someWS lsquare cases:* rsquare someWS timeout someWS contract {% ([{line, col},,,cases,,,timeout,,contract]) => opts.mkTerm(opts.mkWhen(cases)(timeout)(contract))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract).endLineNumber, endColumn: opts.getRange(contract).endColumn}) %}
    | "Let" someWS valueId someWS value someWS contract {% ([{line, col},,valueId,,value,,contract]) => opts.mkTerm(opts.mkLet(valueId)(value)(contract))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract).endLineNumber, endColumn: opts.getRange(contract).endColumn}) %}
    | "Assert" someWS observation someWS contract {% ([{line, col},,observation,,contract]) => opts.mkTerm(opts.mkAssert(observation)(contract))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract).endLineNumber, endColumn: opts.getRange(contract).endColumn}) %}

cases
   -> hole {% ([hole]) => hole %}
    | case {% id %}
    | manyWS %comma manyWS case {% ([,,,case_]) => case_ %}

case
   -> hole {% ([hole]) => hole %}
    | "Case" someWS action someWS contract {% ([{line, col},,action,,contract]) => opts.mkTerm(opts.mkCase(action)(contract))({startLineNumber: line, startColumn: col, endLineNumber: opts.getRange(contract).endLineNumber, endColumn: opts.getRange(contract).endColumn}) %}
    | lparen "Case" someWS action someWS contract rparen {% ([start,,,action,,contract,end]) => opts.mkTerm(opts.mkCase(action)(contract))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

bounds
   -> hole {% ([hole]) => hole %}
    | bound {% id %}
    | manyWS %comma manyWS bound {% ([,,,bound]) => bound %}

bound
   -> hole {% ([hole]) => hole %}
    | "Bound" someWS number someWS number {% ([{line, col},,bottom,,top]) => opts.mkTerm(opts.mkBound(bottom)(top))({startLineNumber: line, startColumn: col, endLineNumber: top.line, endColumn: top.col + top.toString(10).length}) %}
    | lparen bound rparen {% ([,bound,]) => bound %}

action
   -> hole {% ([hole]) => hole %}
    | lparen "Deposit" someWS party someWS party someWS token someWS value rparen {% ([start,{line, col},,account,,party,,token,,value,end]) => opts.mkTerm(opts.mkDeposit(account)(party)(token)(value))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Choice" someWS choiceId someWS lsquare bounds:* rsquare rparen {% ([start,{line, col},,choiceId,,,bounds,,end]) => opts.mkTerm(opts.mkChoice(choiceId)(bounds))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Notify" someWS observation rparen {% ([start,{line, col},,observation,end]) => opts.mkTerm(opts.mkNotify(observation))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

# Beacause top level contracts don't have parenthesis we need to duplicate the lower-level contracts in order to get the start and end positions
contract
   -> hole {% ([hole]) => hole %}
    | "Close" {% ([{line,col}]) => opts.mkTerm(opts.mkClose)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 5}) %}
    | lparen "Pay" someWS party someWS payee someWS token someWS value someWS contract rparen {% ([start,{line, col},,party,,payee,,token,,value,,contract,end]) => opts.mkTerm(opts.mkPay(party)(payee)(token)(value)(contract))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "If" someWS observation someWS contract someWS contract rparen {% ([start,{line, col},,observation,,contract1,,contract2,end]) => opts.mkTerm(opts.mkIf(observation)(contract1)(contract2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "When" someWS lsquare cases:* rsquare someWS timeout someWS contract rparen {% ([start,{line, col},,,cases,,,timeout,,contract,end]) => opts.mkTerm(opts.mkWhen(cases)(timeout)(contract))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Let" someWS valueId someWS value someWS contract rparen {% ([start,{line, col},,valueId,,value,,contract,end]) => opts.mkTerm(opts.mkLet(valueId)(value)(contract))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Assert" someWS observation someWS contract rparen {% ([start,{line, col},,observation,,contract,end]) => opts.mkTerm(opts.mkAssert(observation)(contract))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

choiceId
   -> lparen %CHOICE_ID someWS string someWS party rparen {% ([,{line,col},,cid,,party,]) => opts.mkChoiceId(cid)(party) %}

# FIXME: There is a difference between the Haskell pretty printer and the purescript parser
valueId
   -> %string {% ([{value,line,col}]) => opts.mkTermWrapper(opts.mkValueId(value))({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + value.length}) %}
    | %base16 {% ([{value,line,col}]) => opts.mkTermWrapper(opts.mkValueId(value))({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + value.length}) %}
# valueId -> lparen %VALUE_ID someWS string rparen

token
   -> hole {% ([hole]) => hole %}
    | lparen %TOKEN someWS base16 someWS string rparen {% ([start,{line,col},,a,,b,end]) => opts.mkTerm(opts.mkToken(a)(b))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

party
   -> hole {% ([hole]) => hole %}
    | lparen "PK" someWS base16 rparen {% ([start,{line,col},,k,end]) => opts.mkTerm(opts.mkPK(k))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Role" someWS string rparen {% ([start,{line,col},,k,end]) => opts.mkTerm(opts.mkRole(k))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

payee
   -> hole {% ([hole]) => hole %}
    | lparen "Account" someWS party rparen {% ([start,{line,col},,party,end]) => opts.mkTerm(opts.mkAccount(party))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "Party" someWS party rparen {% ([start,{line,col},,party,end]) => opts.mkTerm(opts.mkParty(party))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}

observation
   -> hole {% ([hole]) => hole %}
    | lparen "AndObs" someWS observation someWS observation rparen {% ([start,{line,col},,o1,,o2,end]) => opts.mkTerm(opts.mkAndObs(o1)(o2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "OrObs" someWS observation someWS observation rparen {% ([start,{line,col},,o1,,o2,end]) => opts.mkTerm(opts.mkOrObs(o1)(o2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "NotObs" someWS observation rparen {% ([start,{line,col},,o1,end]) => opts.mkTerm(opts.mkNotObs(o1))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ChoseSomething" someWS choiceId rparen {% ([start,{line,col},,choiceId,end]) => opts.mkTerm(opts.mkChoseSomething(choiceId))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ValueGE" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkValueGE(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ValueGT" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkValueGT(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ValueLT" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkValueLT(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ValueLE" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkValueLE(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | lparen "ValueEQ" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkValueEQ(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col}) %}
    | "TrueObs" {% ([{line,col}]) => opts.mkTerm(opts.mkTrueObs)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 7}) %}
    | "FalseObs" {% ([{line,col}]) => opts.mkTerm(opts.mkFalseObs)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 8}) %}

rational
    -> hole {% ([hole]) => hole %}
    | number manyWS %ratio manyWS number {%([num,,,,denom]) => opts.mkTerm(opts.mkRational(num)(denom))({startLineNumber: num.line, startColumn: num.col, endLineNumber: denom.line, endColumn: denom.col + denom.toString(10).length}) %}

value
   -> hole {% ([hole]) => hole %}
    | lparen "AvailableMoney" someWS party someWS token rparen {% ([start,{line,col},,party,,token,end]) => opts.mkTerm(opts.mkAvailableMoney(party)(token))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "Constant" someWS number rparen {% ([start,{line,col},,number,end]) => opts.mkTerm(opts.mkConstant(number))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "NegValue" someWS value rparen {% ([start,{line,col},,value,end]) => opts.mkTerm(opts.mkNegValue(value))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "AddValue" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkAddValue(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "SubValue" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkSubValue(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "MulValue" someWS value someWS value rparen {% ([start,{line,col},,v1,,v2,end]) => opts.mkTerm(opts.mkMulValue(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "Scale" someWS lparen rational rparen someWS value rparen {% ([start,{line,col},,,ratio,,,v,end]) => opts.mkTerm(opts.mkScale(ratio)(v))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "ChoiceValue" someWS choiceId rparen {% ([start,{line,col},,choiceId,end]) => opts.mkTerm(opts.mkChoiceValue(choiceId))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | "SlotIntervalStart" {% ([{line,col}]) => opts.mkTerm(opts.mkSlotIntervalStart)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 17}) %}
    | "SlotIntervalEnd" {% ([{line,col}]) => opts.mkTerm(opts.mkSlotIntervalEnd)({startLineNumber: line, startColumn: col, endLineNumber: line, endColumn: col + 15}) %}
    | lparen "UseValue" someWS valueId rparen {% ([start,{line,col},,valueId,end]) => opts.mkTerm(opts.mkUseValue(valueId))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
    | lparen "Cond" someWS observation someWS value someWS value rparen {% ([start,{line,col},,oo,,v1,,v2,end]) => opts.mkTerm(opts.mkCond(oo)(v1)(v2))({startLineNumber: start.line, startColumn: start.col, endLineNumber: end.line, endColumn: end.col + 1}) %}
