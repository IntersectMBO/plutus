import bignumber = require("bignumber.js")

type Party = { "pk_hash" : string }
           | { "role_token" : string };

type SomeNumber = number | string | bigint;

function coerceNumber(n : SomeNumber) : bignumber.BigNumber {
    if (typeof(n) == 'string') {
        return new bignumber.BigNumber(n);
    } else if (typeof(n) == 'bigint') {
        return new bignumber.BigNumber(n.toString());
    } else if (typeof(n) == 'number') {
        if ((n > Number.MAX_SAFE_INTEGER) || (n < -Number.MAX_SAFE_INTEGER)) {
            throw(new Error('Unsafe use of JavaScript numbers. For amounts this large, please use BigNumber.'));
        }
        return new bignumber.BigNumber(n);
    } else {
        throw(new Error('Not a valid number'))
    }
}

export const PK =
    function (pubKey : string) : Party {
        var regexp = /^([0-9a-f][0-9a-f])*$/g;
        if (pubKey.match(regexp)) {
            return { "pk_hash": pubKey };
        } else {
            throw(new Error('Public key must be base16'));
        };
    };

export const Role =
    function (roleToken : string) : Party {
        return { "role_token": roleToken };
    };

type AccountId = Party;

type ChoiceId = { "choice_name" : string,
                  "choice_owner" : Party };

export const ChoiceId =
    function (choiceName : string, choiceOwner : Party) : ChoiceId {
        return { "choice_name": choiceName,
                 "choice_owner": choiceOwner };
    };

type Token = { "currency_symbol": string,
               "token_name": string };

export const Token =
    function (currencySymbol : string, tokenName : string) : Token {
        var regexp = /^([0-9a-f][0-9a-f])*$/g;
        if (currencySymbol.match(regexp)) {
            return { "currency_symbol": currencySymbol,
                     "token_name": tokenName };
        } else {
            throw(new Error('Currency symbol must be base16'));
        };
    };

export const ada : Token = { "currency_symbol": "",
                             "token_name": "" };

type ValueId = string;

export const ValueId =
    function (valueIdentifier : string) : ValueId {
        return valueIdentifier;
    };

type Value = { "amount_of_token": Token,
               "in_account": AccountId }
           | bignumber.BigNumber
           | { "constant_param": String }
           | { "negate": Value }
           | { "add": Value
             , "and": Value }
           | { "value": Value
             , "minus": Value }
           | { "multiply": Value
             , "times": Value }
           | { "multiply": Value
             , "times": bignumber.BigNumber
             , "divide_by": bignumber.BigNumber }
           | { "value_of_choice": ChoiceId }
           | "slot_interval_start"
           | "slot_interval_end"
           | { "use_value": ValueId }
           | { "if": Observation
             , "then": Value
             , "else": Value };

type EValue = SomeNumber | Value;

function coerceValue(val : EValue) : Value {
    if (typeof(val) == "number") {
        if ((val > Number.MAX_SAFE_INTEGER) || (val < -Number.MAX_SAFE_INTEGER)) {
            throw(new Error('Unsafe use of JavaScript numbers. For amounts this large, please use BigNumber.'));
        }
        return new bignumber.BigNumber(val);
    } else if (typeof(val) == 'bigint') {
        return new bignumber.BigNumber(val.toString());
    } else if (typeof(val) == "string" && val != "slot_interval_start" && val != "slot_interval_end") {
        return new bignumber.BigNumber(val);
    } else {
        return val;
    }
}

export const AvailableMoney =
    function (token : Token, accountId : AccountId) : Value {
        return { "amount_of_token": token,
                 "in_account": accountId };
    };

export const Constant =
    function (number : SomeNumber) : Value {
        return coerceNumber(number);
    };

export const ConstantParam =
    function (paramName : String) : Value {
        return { "constant_param": paramName };
    };

export const NegValue =
    function (value : EValue) : Value {
        return { "negate": coerceValue(value) };
    };

export const AddValue =
    function (lhs : EValue, rhs : EValue) : Value {
        return { "add": coerceValue(lhs),
                 "and": coerceValue(rhs) };
    };

export const SubValue =
    function (lhs : EValue, rhs : EValue) : Value {
        return { "value": coerceValue(lhs),
                 "minus": coerceValue(rhs) };
    };

export const MulValue =
    function (lhs : EValue, rhs : EValue) : Value {
        return { "multiply": coerceValue(lhs),
                 "times": coerceValue(rhs) };
    };

export const Scale =
    function (num : SomeNumber, den : SomeNumber, val : EValue) : Value {
        var cden = coerceNumber(den);
        if (cden <= (new bignumber.BigNumber(0))) {
            throw(new Error("Denominator in scale must be strictly positve"));
        } else {
            return { "multiply": coerceValue(val),
                    "times": coerceNumber(num),
                    "divide_by": cden };
        }
    };

export const ChoiceValue =
    function (choiceId : ChoiceId) : Value {
        return { "value_of_choice": choiceId };
    };

export const SlotIntervalStart : Value = "slot_interval_start";

export const SlotIntervalEnd : Value = "slot_interval_end";

export const UseValue =
    function (valueId : ValueId) : Value {
        return { "use_value": valueId };
    };

export const Cond =
    function (obs : Observation, contThen : EValue, contElse : EValue) : Value {
        return { "if": obs,
                 "then": coerceValue(contThen),
                 "else": coerceValue(contElse) }
    };

type Observation = { "both": Observation,
                     "and": Observation }
                 | { "either": Observation,
                     "or": Observation }
                 | { "not": Observation }
                 | { "chose_something_for": ChoiceId }
                 | { "value": Value,
                     "ge_than": Value }
                 | { "value": Value,
                     "gt": Value }
                 | { "value": Value,
                     "lt": Value }
                 | { "value": Value,
                     "le_than": Value }
                 | { "value": Value,
                     "equal_to": Value }
                 | boolean;

export const AndObs =
    function (lhs : Observation, rhs : Observation) : Observation {
        return { "both": lhs,
                 "and": rhs };
    };

export const OrObs =
    function (lhs : Observation, rhs : Observation) : Observation {
        return { "either": lhs,
                 "or": rhs };
    };

export const NotObs =
    function (obs : Observation) : Observation {
        return { "not": obs };
    };

export const ChoseSomething =
    function (choiceId : ChoiceId) : Observation {
        return { "chose_something_for": choiceId };
    };

export const ValueGE =
    function (lhs : EValue, rhs : EValue) : Observation {
        return { "value": coerceValue(lhs),
                 "ge_than": coerceValue(rhs) };
    };

export const ValueGT =
    function (lhs : EValue, rhs : EValue) : Observation {
        return { "value": coerceValue(lhs),
                 "gt": coerceValue(rhs) };
    };

export const ValueLT =
    function (lhs : EValue, rhs : EValue) : Observation {
        return { "value": coerceValue(lhs),
                 "lt": coerceValue(rhs) };
    };

export const ValueLE =
    function (lhs : EValue, rhs : EValue) : Observation {
        return { "value": coerceValue(lhs),
                 "le_than": coerceValue(rhs) };
    };

export const ValueEQ =
    function (lhs : EValue, rhs : EValue) : Observation {
        return { "value": coerceValue(lhs),
                 "equal_to": coerceValue(rhs) };
    };

export const TrueObs : Observation = true;

export const FalseObs : Observation = false;

type Bound = { "from": bignumber.BigNumber,
               "to": bignumber.BigNumber };

export const Bound =
    function (boundMin : SomeNumber, boundMax : SomeNumber) : Bound {
        return { "from": coerceNumber(boundMin),
                 "to": coerceNumber(boundMax) };
    };

type Action = { "party": Party,
                "deposits": Value,
                "of_token": Token,
                "into_account": AccountId }
            | { "choose_between": Bound[],
                "for_choice": ChoiceId }
            | { "notify_if": Observation };

export const Deposit =
    function (accId : AccountId, party : Party, token : Token, value : EValue) : Action {
        return { "party": party,
                 "deposits": coerceValue(value),
                 "of_token": token,
                 "into_account": accId };
    };

export const Choice =
    function (choiceId : ChoiceId, bounds : Bound[]) : Action {
        return { "choose_between": bounds,
                 "for_choice": choiceId };
    };

export const Notify =
    function (obs : Observation) : Action {
        return { "notify_if": obs };
    };

type Payee = { "account" : AccountId }
           | { "party" : Party };

export function Account(party: Party) : Payee {
    return { "account" : party };
}

export function Party(party: Party) : Payee {
  return { "party" : party };
}

type Case = { "case": Action,
              "then": Contract };

export const Case =
    function (caseAction : Action, continuation : Contract) : Case {
        return { "case": caseAction,
                 "then": continuation };
    };

type Timeout = { "slot_param": String }
             | bignumber.BigNumber;

type ETimeout = SomeNumber | Timeout;

export const SlotParam =
    function (paramName : String) : Timeout {
        return { "slot_param": paramName }
    }

type Contract = "close"
              | { "pay": Value,
                  "token": Token,
                  "from_account": AccountId,
                  "to": Payee,
                  "then": Contract }
              | { "if": Observation,
                  "then": Contract,
                  "else": Contract }
              | { "when": Case [],
                  "timeout": Timeout,
                  "timeout_continuation": Contract }
              | { "let": ValueId,
                  "be": Value,
                  "then": Contract }
              | { "assert": Observation,
                  "then": Contract };

export const Close : Contract = "close";

export const Pay =
    function (accId : AccountId, payee : Payee, token : Token,
              value : EValue, continuation : Contract) : Contract {
        return { "pay": coerceValue(value),
                 "token": token,
                 "from_account": accId,
                 "to": payee,
                 "then": continuation };
    };

export const If =
    function (obs : Observation, contThen : Contract, contElse : Contract) : Contract {
        return { "if": obs,
                 "then": contThen,
                 "else": contElse };
    };

export const When =
    function (cases : Case[], timeout : ETimeout, timeoutCont : Contract) : Contract {
        var coercedTimeout : Timeout;
        if (typeof (timeout) == "object") { coercedTimeout = timeout; } else { coercedTimeout = coerceNumber(timeout); }
        return { "when": cases,
                 "timeout": coercedTimeout,
                 "timeout_continuation": timeoutCont };
    };

export const Let =
    function (valueId : ValueId, value : Value, cont : Contract) : Contract {
        return { "let": valueId,
                 "be": value,
                 "then": cont };
    };

export const Assert =
    function (obs : Observation, cont : Contract) : Contract {
        return { "assert": obs,
                 "then": cont };
    };
