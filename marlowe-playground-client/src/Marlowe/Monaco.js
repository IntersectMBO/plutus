/*eslint-env node*/
'use strict';

const monaco = require('src/Marlowe/Monaco.ts');

exports.hoverProvider_ = function (hoverProvider) {
    return new monaco.MarloweHoverProvider(hoverProvider);
}

exports.completionItemProvider_ = function (suggestionsProvider) {
    let uncurriedSuggestions = (word, stripParens, contract, range, context) => suggestionsProvider(word)(stripParens)(contract)(range)(context);
    return new monaco.MarloweCompletionItemProvider(uncurriedSuggestions);
}

exports.codeActionProvider_ = function (provideCodeActions, additionalContext) {
    let uncurriedProvideCodeActions = (a, b, c) => provideCodeActions(a)(b)(c);
    return new monaco.MarloweCodeActionProvider(uncurriedProvideCodeActions, additionalContext);
}

exports.updateAdditionalContext_ = function (codeActionProvider, completionItemProvider, additionalContext) {
    codeActionProvider.updateAdditionalContext(additionalContext);
    completionItemProvider.updateAdditionalContext(additionalContext);
}

exports.documentFormattingEditProvider_ = function (format) {
    return new monaco.MarloweDocumentFormattingEditProvider(format);
}

exports.tokensProvider = new monaco.MarloweTokensProvider();

const purple = "#832DC4";
const orange = "#EB4A22";
const darkGreen = "#007600";
const lightGreen = "#2CBB69";
const blue = "#1746A0";
const red = "#EB2256";
const grey = "#AAAAAA";

exports.daylightTheme_ = {
    base: 'vs',
    inherit: true,
    rules: [
        { token: '', foreground: red, background: 'fffffe' },
        { token: "number", foreground: purple },
        { token: "string", foreground: orange },
        { token: "ratio", foreground: darkGreen },
        { token: "comma", foreground: darkGreen },
        { token: "lparen", foreground: darkGreen },
        { token: "rparen", foreground: darkGreen },
        { token: "lsquare", foreground: darkGreen },
        { token: "rsquare", foreground: darkGreen },
        { token: "comment", foreground: grey },
        { token: "hole", foreground: lightGreen, fontStyle: 'italic' },
        { token: "CONTRACT", foreground: blue },
        { token: "OBSERVATION", foreground: blue },
        { token: "VALUE", foreground: blue },
        { token: "ACCOUNT_ID", foreground: blue },
        { token: "TOKEN", foreground: blue },
        { token: "PAYEE", foreground: blue },
        { token: "PARTY", foreground: blue },
        { token: "BOUND", foreground: blue },
        { token: "TIMEOUT", foreground: blue },
        { token: "VALUE_ID", foreground: blue },
        { token: "CASE", foreground: blue },
        { token: "ACTION", foreground: blue },
        { token: "CHOICE_ID", foreground: blue },
    ],
}