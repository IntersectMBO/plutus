/*eslint-env node*/
/*global global*/
import '@fortawesome/fontawesome-free/css/all.css';
import './static/css/main.scss';
import 'blockly';

import './grammar.ne';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
global.monaco = monaco;
import { EmacsExtension } from 'monaco-emacs';
global.EmacsExtension = EmacsExtension;
import { initVimMode } from 'monaco-vim';
global.initVimMode = initVimMode;

import * as bignumberDTS from '!!raw-loader!bignumber.js/bignumber.d.ts';
import * as marloweDTS from '!!raw-loader!src/Language/Javascript/MarloweJS.ts';
global.monacoExtraTypeScriptLibs = [
  [ bignumberDTS.default, 'inmemory://model/bignumber.js.d.ts'],
  [ marloweDTS.default, "inmemory://model/marlowe-js.d.ts" ]
];

import { BigNumber } from 'bignumber';

import './src/Main.purs';
