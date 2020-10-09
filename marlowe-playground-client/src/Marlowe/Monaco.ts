import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
import * as moo from 'moo';

export class MarloweHoverProvider implements monaco.languages.HoverProvider {

  // This enables us to pass in a function from PureScript that provides hover information
  hoverProvider: (word: string) => monaco.languages.Hover

  constructor (hoverProvider) {
    this.hoverProvider = hoverProvider;
  }
  provideHover (model: monaco.editor.ITextModel, position: monaco.Position, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.Hover> {
    const word = model.getWordAtPosition(position);
    return word ? this.hoverProvider(word.word) : null
  }

}

// This is a purescript type at runtime but we don't know anything about it, so we just tag any
type AdditionalContext = any

export class MarloweCompletionItemProvider implements monaco.languages.CompletionItemProvider {

  // This enables us to pass in a function from PureScript that provides suggestions based on a contract string
  suggestionsProvider: (String, Boolean, string, IRange, additionalContext: AdditionalContext) => Array<monaco.languages.CompletionItem>

  additionalContext: AdditionalContext

  constructor (suggestionsProvider) {
    this.suggestionsProvider = suggestionsProvider;
    this.additionalContext = {}
  }

  updateAdditionalContext (additionalContext) {
    this.additionalContext = additionalContext
  }

  provideCompletionItems (model: monaco.editor.ITextModel, position: monaco.Position, context: monaco.languages.CompletionContext, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.CompletionList> {
    var word = model.getWordAtPosition(position);
    const isEmptyWord = word == null;
    // if the word is empty then we need an extra space in the contract that we generate
    const emptyWordHack = isEmptyWord ? " " : ""
    if (isEmptyWord) {
      word = {
        // for some reason an empty string here doesn't work so we give it a dummy value
        word: "*",
        startColumn: position.column,
        endColumn: position.column,
      }
    }
    const stripParens = word.startColumn == 1 && position.lineNumber == 1;
    const wordStart = model.getOffsetAt(position);
    const wordEnd = wordStart + word.word.length;
    // because of the dummy * value we need to mess with the substring lengths
    const offset = isEmptyWord ? 0 : word.word.length;
    const startOfContract = model.getValue().substring(0, wordStart - offset);
    const endOfContract = model.getValue().substring(wordEnd - 1);
    // we replace the word at the cursor with a hole with a special name so that the contract is parsable
    // if the contract is not valid then we won't get any suggestions
    const contract = startOfContract + emptyWordHack + "?monaco_suggestions" + endOfContract;

    const range = {
      startLineNumber: position.lineNumber,
      startColumn: word.startColumn,
      endLineNumber: position.lineNumber,
      endColumn: word.endColumn
    }

    return { suggestions: this.suggestionsProvider(word.word, stripParens, contract, range, this.additionalContext) };
  }

}

export class MarloweCodeActionProvider implements monaco.languages.CodeActionProvider {

  actionsProvider: (uri: monaco.Uri, marloweType: Array<monaco.editor.IMarkerData>, additionalContext: AdditionalContext) => Array<monaco.languages.CodeAction>

  additionalContext: AdditionalContext

  constructor (actionsProvider, additionalContext) {
    this.actionsProvider = actionsProvider
    this.additionalContext = additionalContext
  }

  updateAdditionalContext (additionalContext) {
    this.additionalContext = additionalContext
  }

  provideCodeActions (model: monaco.editor.ITextModel, range: monaco.Range, context: monaco.languages.CodeActionContext, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.CodeActionList> {
    // create actions for all the markers
    const actions = this.actionsProvider(model.uri, context.markers, this.additionalContext);
    return {
      actions: actions,
      dispose: () => { }
    };
  }
}

export class MarloweDocumentFormattingEditProvider implements monaco.languages.DocumentFormattingEditProvider {
  format: (contractString: string) => string

  constructor (format: (contractString: string) => string) {
    this.format = format;
  }

  displayName: "Marlowe";

  provideDocumentFormattingEdits (model: monaco.editor.ITextModel, options: monaco.languages.FormattingOptions, token: monaco.CancellationToken): monaco.languages.ProviderResult<monaco.languages.TextEdit[]> {
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

  constructor (lexer: any) {
    this.lexer = lexer;
  }
  clone (): monaco.languages.IState {
    return new MarloweTokensState(this.lexer);
  }
  equals (other: MarloweTokensState): boolean {
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
        'ChoiceValue',
        'SlotIntervalStart',
        'SlotIntervalEnd',
        'UseValue',
        'Cond',
        'Scale',
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
  myError: { match: /[\$?`]/, error: true },
});

interface ILexResult { offset: number, type: string }

export class MarloweTokensProvider implements monaco.languages.TokensProvider {

  getInitialState (): MarloweTokensState {
    return new MarloweTokensState(marloweLexer);
  }

  tokenize (line: string, state: MarloweTokensState): monaco.languages.ILineTokens {
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
