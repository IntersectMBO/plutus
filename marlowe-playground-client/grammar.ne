@{%
const moo = require("moo");

const lexer = moo.compile({
        WS: /[ \t]+/,
        number: /0|-?[1-9][0-9]*/,
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
                CONTRACT: ['Close', 'Pay', 'If', 'When', 'Let'],
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
                    'Scale',
                    'ChoiceValue',
                    'SlotIntervalStart',
                    'SlotIntervalEnd',
                    'UseValue',
                ],
                ACCOUNT_ID: ['AccountId'],
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

lparen -> %lparen  manyWS

rparen ->  manyWS %rparen

lsquare -> %lsquare manyWS

rsquare ->  manyWS %rsquare

hole -> %hole {% ([hole]) => opts.mkHole(hole.value.substring(1))({row: hole.line, column: hole.col}) %}

number
   -> %number {% ([n]) => opts.mkBigInteger(n.value) %}
    | lparen %number rparen {% ([,n,]) => opts.mkBigInteger(n.value) %}

timeout
   -> %number {% ([n]) => opts.mkTimeout(n.value)({row: n.line, column: n.col}) %}
    | lparen %number rparen {% ([,n,]) => opts.mkTimeout(n.value)({row: n.line, column: n.col}) %}

string
   -> %string {% ([s]) => s.value %}

topContract
   -> hole {% ([hole]) => hole %}
    | "Close" {% ([{line, col}]) => opts.mkTerm(opts.mkClose)({row: line, column: col}) %}
    | "Pay" someWS accountId someWS payee someWS token someWS value someWS contract {% ([{line, col},,accountId,,payee,,token,,value,,contract]) => opts.mkTerm(opts.mkPay(accountId)(payee)(token)(value)(contract))({row: line, column: col}) %}
    | "If" someWS observation someWS contract someWS contract {% ([{line, col},,observation,,contract1,,contract2]) => opts.mkTerm(opts.mkIf(observation)(contract1)(contract2))({row: line, column: col}) %}
    | "When" someWS lsquare cases:* rsquare someWS timeout someWS contract {% ([{line, col},,,cases,,,timeout,,contract]) => opts.mkTerm(opts.mkWhen(cases)(timeout)(contract))({row: line, column: col}) %}
    | "Let" someWS valueId someWS value someWS contract {% ([{line, col},,valueId,,value,,contract]) => opts.mkTerm(opts.mkLet(valueId)(value)(contract))({row: line, column: col}) %}

cases
   -> hole {% ([hole]) => hole %}
    | case {% id %}
    | manyWS %comma manyWS case {% ([,,,case_]) => case_ %}

case
   -> hole {% ([hole]) => hole %}
    | "Case" someWS action someWS contract {% ([{line, col},,action,,contract]) => opts.mkTerm(opts.mkCase(action)(contract))({row: line, column: col}) %}
    | lparen case rparen {% ([,case_,]) => case_ %}

bounds
   -> hole {% ([hole]) => hole %}
    | bound {% id %}
    | manyWS %comma manyWS bound {% ([,,,bound]) => bound %}

bound
   -> hole {% ([hole]) => hole %}
    | "Bound" someWS number someWS number {% ([{line, col},,bottom,,top]) => opts.mkTerm(opts.mkBound(bottom)(top))({row: line, column: col}) %}
    | lparen bound rparen {% ([,bound,]) => bound %}

action
   -> hole {% ([hole]) => hole %}
    | lparen "Deposit" someWS accountId someWS party someWS token someWS value rparen {% ([,{line, col},,accountId,,party,,token,,value,]) => opts.mkTerm(opts.mkDeposit(accountId)(party)(token)(value))({row: line, column: col}) %}
    | lparen "Choice" someWS choiceId someWS lsquare bounds:* rsquare rparen {% ([,{line, col},,choiceId,,,bounds,,]) => opts.mkTerm(opts.mkChoice(choiceId)(bounds))({row: line, column: col}) %}
    | lparen "Notify" someWS observation rparen {% ([,{line, col},,observation,]) => opts.mkTerm(opts.mkNotify(observation))({row: line, column: col}) %}

# Beacause top level contracts don't have parenthesis we need to duplicate the lower-level contracts that don't have parenthesis here
contract
   -> hole {% ([hole]) => hole %}
    | "Close" {% ([{line,col}]) => opts.mkTerm(opts.mkClose)({row: line, column: col}) %}
    | lparen topContract rparen {% ([,contract,]) => contract %}

choiceId
   -> hole {% ([hole]) => hole %}
    | lparen %CHOICE_ID someWS string someWS party rparen {% ([,{line,col},,cid,,party,]) => opts.mkTerm(opts.mkChoiceId(cid)(party))({row: line, column: col}) %}

# FIXME: There is a difference between the Haskell pretty printer and the purescript parser
valueId
   -> %string {% ([{value,line,col}]) => opts.mkTermWrapper(opts.mkValueId(value))({row: line, column: col}) %}
# valueId -> lparen %VALUE_ID someWS string rparen

accountId
   -> hole {% ([hole]) => hole %}
    | lparen %ACCOUNT_ID someWS number someWS party rparen {% ([,{line,col},,aid,,party,]) => opts.mkTerm(opts.mkAccountId(aid)(party))({row: line, column: col}) %}

token
   -> hole {% ([hole]) => hole %}
    | lparen %TOKEN someWS string someWS string rparen {% ([,{line,col},,a,,b,]) => opts.mkTerm(opts.mkToken(a)(b))({row: line, column: col}) %}

party
   -> hole {% ([hole]) => hole %}
    | lparen "PK" someWS string rparen {% ([,{line,col},,k,]) => opts.mkTerm(opts.mkPK(k))({row: line, column: col}) %}
    | lparen "Role" someWS string rparen {% ([,{line,col},,k,]) => opts.mkTerm(opts.mkRole(k))({row: line, column: col}) %}

payee
   -> hole {% ([hole]) => hole %}
    | lparen "Account" someWS accountId rparen {% ([,{line,col},,accountId,]) => opts.mkTerm(opts.mkAccount(accountId))({row: line, column: col}) %}
    | lparen "Party" someWS party rparen {% ([,{line,col},,party,]) => opts.mkTerm(opts.mkParty(party))({row: line, column: col}) %}

observation
   -> hole {% ([hole]) => hole %}
    | lparen "AndObs" someWS observation someWS observation rparen {% ([,{line,col},,o1,,o2,]) => opts.mkTerm(opts.mkAndObs(o1)(o2))({row: line, column: col}) %}
    | lparen "OrObs" someWS observation someWS observation rparen {% ([,{line,col},,o1,,o2,]) => opts.mkTerm(opts.mkOrObs(o1)(o2))({row: line, column: col}) %}
    | lparen "NotObs" someWS observation rparen {% ([,{line,col},,o1,]) => opts.mkTerm(opts.mkNotObs(o1))({row: line, column: col}) %}
    | lparen "ChoseSomething" someWS choiceId rparen {% ([,{line,col},,choiceId,]) => opts.mkTerm(opts.mkChoseSomething(choiceId))({row: line, column: col}) %}
    | lparen "ValueGE" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkValueGE(v1)(v2))({row: line, column: col}) %}
    | lparen "ValueGT" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkValueGT(v1)(v2))({row: line, column: col}) %}
    | lparen "ValueLT" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkValueLT(v1)(v2))({row: line, column: col}) %}
    | lparen "ValueLE" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkValueLE(v1)(v2))({row: line, column: col}) %}
    | lparen "ValueEQ" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkValueEQ(v1)(v2))({row: line, column: col}) %}
    | "TrueObs" {% ([{line,col}]) => opts.mkTerm(opts.mkTrueObs)({row: line, column: col}) %}
    | "FalseObs" {% ([{line,col}]) => opts.mkTerm(opts.mkFalseObs)({row: line, column: col}) %}

rational
    -> hole {% ([hole]) => hole %}
    | %number manyWS "%" manyWS %number {%([num,,,,denom,]) => opts.mkTerm(opts.mkRational(num.value)(denom.value))({row: num.line, column: num.col}) %}

value
   -> hole {% ([hole]) => hole %}
    | lparen "AvailableMoney" someWS accountId someWS token rparen {% ([,{line,col},,accountId,,token,]) => opts.mkTerm(opts.mkAvailableMoney(accountId)(token))({row: line, column: col}) %}
    | lparen "Constant" someWS number rparen {% ([,{line,col},,number,]) => opts.mkTerm(opts.mkConstant(number))({row: line, column: col}) %}
    | lparen "NegValue" someWS value rparen {% ([,{line,col},,value,]) => opts.mkTerm(opts.mkNegValue(value))({row: line, column: col}) %}
    | lparen "AddValue" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkAddValue(v1)(v2))({row: line, column: col}) %}
    | lparen "SubValue" someWS value someWS value rparen {% ([,{line,col},,v1,,v2,]) => opts.mkTerm(opts.mkSubValue(v1)(v2))({row: line, column: col}) %}
    | lparen "Scale" someWS lparen rational rparen someWS value rparen {% ([,{line,col},,,ratio,,,v,]) => opts.mkTerm(opts.mkScale(ratio)(v))({row: line, column: col}) %}
    | lparen "ChoiceValue" someWS choiceId someWS value rparen {% ([,{line,col},,choiceId,,value,]) => opts.mkTerm(opts.mkChoiceValue(choiceId)(value))({row: line, column: col}) %}
    | "SlotIntervalStart" {% ([{line,col}]) => opts.mkTerm(opts.mkSlotIntervalStart)({row: line, column: col}) %}
    | "SlotIntervalEnd" {% ([{line,col}]) => opts.mkTerm(opts.mkSlotIntervalEnd)({row: line, column: col}) %}
    | lparen "UseValue" someWS valueId rparen {% ([,{line,col},,valueId,]) => opts.mkTerm(opts.mkUseValue(valueId))({row: line, column: col}) %}
