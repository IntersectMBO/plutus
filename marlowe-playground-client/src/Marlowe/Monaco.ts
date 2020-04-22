import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
import * as moo from 'moo';

export class MarloweCompletionItemProvider implements monaco.languages.CompletionItemProvider {

  // This enables us to pass in a function from PureScript that provides suggestions based on a contract string
  suggestionsProvider: (Boolean, string, IRange) => Array<monaco.languages.CompletionItem>

  constructor(suggestionsProvider) {
    this.suggestionsProvider = suggestionsProvider;
  }

  provideCompletionItems(model: monaco.editor.ITextModel, position: monaco.Position, context: monaco.languages.CompletionContext, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.CompletionList> {
    const word = model.getWordAtPosition(position);
    const stripParens = word.startColumn == 1 && position.lineNumber == 1;
    const wordStart = model.getOffsetAt(position);
    const wordEnd = wordStart + word.word.length;
    const startOfContract = model.getValue().substring(0, wordStart - 1);
    const endOfContract = model.getValue().substring(wordEnd - 1);

    // we replace the word at the cursor with a hole with a special name so that the contract is parsable
    // if the contract is not valid then we won't get any suggestions
    const contract = startOfContract + "?monaco_suggestions" + endOfContract;

    const range = {
      startLineNumber: position.lineNumber,
      startColumn: word.startColumn,
      endLineNumber: position.lineNumber,
      endColumn: word.endColumn
    }

    return { suggestions: this.suggestionsProvider(stripParens, contract, range) };
  }

}

export class MarloweCodeActionProvider implements monaco.languages.CodeActionProvider {
  actionsProvider: (uri: monaco.Uri, marloweType: Array<monaco.editor.IMarkerData>) => Array<monaco.languages.CodeAction>

  constructor(actionsProvider) {
    this.actionsProvider = actionsProvider
  }

  provideCodeActions(model: monaco.editor.ITextModel, range: monaco.Range, context: monaco.languages.CodeActionContext, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.CodeActionList> {
    // create actions for all the markers
    // console.log(context);
    const actions = this.actionsProvider(model.uri, context.markers);
    return {
      actions: actions,
      dispose: () => { }
    };
  }
}

export class MarloweDocumentFormattingEditProvider implements monaco.languages.DocumentFormattingEditProvider {
  format: (contractString: string) => string

  constructor(format: (contractString: string) => string) {
    this.format = format;
  }

  displayName: "Marlowe";

  provideDocumentFormattingEdits(model: monaco.editor.ITextModel, options: monaco.languages.FormattingOptions, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.TextEdit[]> {
    const range = model.getFullModelRange();
    const text = this.format(model.getValue());
    return [{
      range,
      text
    }]
  }

}

export class MarloweTokensState implements monaco.languages.IState {
  lexer: any;

  constructor(lexer: any) {
    this.lexer = lexer;
  }
  clone(): monaco.languages.IState {
    return new MarloweTokensState(this.lexer);
  }
  equals(other: MarloweTokensState): boolean {
    return (other === this || other.lexer === this.lexer);
  }


}

const marloweLexer = moo.compile({
  WS: /[ \t]+/,
  number: /0|-?[1-9][0-9]*/,
  string: { match: /"(?:\\["\\]|[^\n"\\])*"/, value: x => x.slice(1, -1) },
  ratio: '%',
  comma: ',',
  lparen: '(',
  rparen: ')',
  lsquare: '[',
  rsquare: ']',
  comment: /--.*/,
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
        'ChoiceValue',
        'SlotIntervalStart',
        'SlotIntervalEnd',
        'UseValue',
        'Scale',
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
  myError: { match: /[\$?`]/, error: true },
});

interface ILexResult { offset: number, type: string }

export class MarloweTokensProvider implements monaco.languages.TokensProvider {

  getInitialState(): MarloweTokensState {
    return new MarloweTokensState(marloweLexer);
  }

  tokenize(line: string, state: MarloweTokensState): monaco.languages.ILineTokens {
    let lexer = state.lexer;
    lexer.reset(line);
    let result: Array<ILexResult> = Array.from(lexer);
    let monacoTokens = result.map(t => ({
      startIndex: t.offset,
      scopes: t.type,
    }));
    return {
      endState: new MarloweTokensState(lexer),
      tokens: monacoTokens,
    }
  }

}