import bignumber = require("bignumber")

type Party = { "pk_hash" : string }
           | { "role_token" : string };

export const pk =
    function (pubKey : string) : Party {
        var regexp = /^([0-9a-f][0-9a-f])*$/g;
        if (pubKey.match(regexp)) {
            return { "pk_hash": pubKey };
        } else {
            throw(new Error('Public key must be base16'));
        };
    };

export const role =
    function (roleToken : string) : Party {
        return { "role_token": roleToken };
    };

type AccountId = { "account_number" : string,
                   "account_owner" : Party };

export const accountId =
    function (accountNumber : bignumber.BigNumber, accountOwner : Party) : AccountId {
        return { "account_number": accountNumber.toString(),
                 "account_owner": accountOwner };
    };

type ChoiceId = { "choice_name" : string,
                  "choice_owner" : Party };

export const choiceId =
    function (choiceName : string, choiceOwner : Party) : ChoiceId {
        return { "choice_name": choiceName,
                 "choice_owner": choiceOwner };
    };

type Token = { "currency_symbol": string,
               "token_name": string };

export const token =
    function (currencySymbol : string, choiceOwner : string) : Token {
        var regexp = /^([0-9a-f][0-9a-f])*$/g;
        if (currencySymbol.match(regexp)) {
            return { "currency_symbol": currencySymbol,
                     "token_name": choiceOwner };
        } else {
            throw(new Error('Currency symbol must be base16'));
        };
    };

export const ada : Token = { "currency_symbol": "",
                             "token_name": "" };

type ValueId = string;

export const valueId =
    function (valueIdentifier : string) : ValueId {
        return valueIdentifier;
    };

type Value = { "amount_of_token": Token,
               "in_account": AccountId }
           | string
           | { "negate": Value }
           | { "add": Value
             , "and": Value }
           | { "value": Value
             , "minus": Value }
           | { "multiply": Value
             , "times": Value }
           | { "multiply": Value
             , "times": string
             , "divide_by": string }
           | { "value_of_choice": ChoiceId }
           | "slot_interval_start"
           | "slot_interval_end"
           | { "use_value": ValueId }
           | { "if": Observation
             , "then": Value
             , "else": Value };

export const availableMoney =
    function (token : Token, accountId : AccountId) : Value {
        return { "amount_of_token": token,
                 "in_account": accountId };
    };

export const constant =
    function (number : bignumber.BigNumber) : Value {
        return number.toString();
    };

export const negValue =
    function (value : Value) : Value {
        return { "negate": value };
    };

export const addValue =
    function (lhs : Value, rhs : Value) : Value {
        return { "add": lhs,
                 "and": rhs };
    };

export const subValue =
    function (lhs : Value, rhs : Value) : Value {
        return { "value": lhs,
                 "minus": rhs };
    };

export const mulValue =
    function (lhs : Value, rhs : Value) : Value {
        return { "multiply": lhs,
                 "times": rhs };
    };

export const scale =
    function (num : bignumber.BigNumber, den : bignumber.BigNumber, val : Value) : Value {
        if (den.leq(bignumber.zero)) {
            throw(new Error("Denominator in scale must be strictly positve"));
        } else {
            return { "multiply": val,
                    "times": num.toString(),
                    "divide_by": den.toString() };
        }
    };

export const choiceValue =
    function (choiceId : ChoiceId) : Value {
        return { "value_of_choice": choiceId };
    };

export const slotIntervalStart : Value = "slot_interval_start";

export const slotIntervalEnd : Value = "slot_interval_end";

export const useValue =
    function (valueId : ValueId) : Value {
        return { "use_value": valueId };
    };

export const cond =
    function (obs : Observation, contThen : Value, contElse : Value) : Value {
        return { "if": obs,
                 "then": contThen,
                 "else": contElse }
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

export const andObs =
    function (lhs : Observation, rhs : Observation) : Observation {
        return { "both": lhs,
                 "and": rhs };
    };

export const orObs =
    function (lhs : Observation, rhs : Observation) : Observation {
        return { "either": lhs,
                 "or": rhs };
    };

export const notObs =
    function (obs : Observation) : Observation {
        return { "not": obs };
    };

export const choseSomething =
    function (choiceId : ChoiceId) : Observation {
        return { "chose_something_for": choiceId };
    };

export const valueGE =
    function (lhs : Value, rhs : Value) : Observation {
        return { "value": lhs,
                 "ge_than": rhs };
    };

export const valueGT =
    function (lhs : Value, rhs : Value) : Observation {
        return { "value": lhs,
                 "gt": rhs };
    };

export const valueLT =
    function (lhs : Value, rhs : Value) : Observation {
        return { "value": lhs,
                 "lt": rhs };
    };

export const valueLE =
    function (lhs : Value, rhs : Value) : Observation {
        return { "value": lhs,
                 "le_than": rhs };
    };

export const valueEQ =
    function (lhs : Value, rhs : Value) : Observation {
        return { "value": lhs,
                 "equal_to": rhs };
    };

export const trueObs : Observation = true;

export const falseObs : Observation = false;

type Bound = { "from": String,
               "to": String };

export const bound =
    function (boundMin : bignumber.BigNumber, boundMax : bignumber.BigNumber) : Bound {
        return { "from": boundMin.toString(),
                 "to": boundMax.toString() };
    };

type Action = { "party": Party,
                "deposits": Value,
                "of_token": Token,
                "into_account": AccountId }
            | { "choose_between": Bound[],
                "for_choice": ChoiceId }
            | { "notify_if": Observation };

export const deposit =
    function (accId : AccountId, party : Party, token : Token, value : Value) : Action {
        return { "party": party,
                 "deposits": value,
                 "of_token": token,
                 "into_account": accId };
    };

export const choice =
    function (choiceId : ChoiceId, bounds : Bound[]) : Action {
        return { "choose_between": bounds,
                 "for_choice": choiceId };
    };

export const notify =
    function (obs : Observation) : Action {
        return { "notify_if": obs };
    };

type Payee = AccountId
           | Party;

type Case = { "case": Action,
              "then": Contract };

export const caseM =
    function (caseAction : Action, continuation : Contract) : Case {
        return { "case": caseAction,
                 "then": continuation };
    };

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
                  "timeout": string,
                  "timeout_continuation": Contract }
              | { "let": ValueId,
                  "be": Value,
                  "then": Contract }
              | { "assert": Observation,
                  "then": Contract };

export const closeM : Contract = "close";

export const payM =
    function (accId : AccountId, payee : Payee, token : Token,
              value : Value, continuation : Contract) : Contract {
        return { "pay": value,
                 "token": token,
                 "from_account": accId,
                 "to": payee,
                 "then": continuation };
    };

export const ifM =
    function (obs : Observation, contThen : Contract, contElse : Contract) : Contract {
        return { "if": obs,
                 "then": contThen,
                 "else": contElse };
    };

export const whenM =
    function (cases : Case[], timeout : bignumber.BigNumber, timeoutCont : Contract) : Contract {
        return { "when": cases,
                 "timeout": timeout.toString(),
                 "timeout_continuation": timeoutCont };
    };

export const letM =
    function (valueId : ValueId, value : Value, cont : Contract) : Contract {
        return { "let": valueId,
                 "be": value,
                 "then": cont };
    };

export const assertM =
    function (obs : Observation, cont : Contract) : Contract {
        return { "assert": obs,
                 "then": cont };
    };
