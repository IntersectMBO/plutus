import '@fortawesome/fontawesome-free/css/all.css';
import './static/css/main.scss';

import 'ace-builds/src-min-noconflict/ace.js';
import 'ace-builds/src-min-noconflict/mode-haskell.js';
import 'ace-builds/src-min-noconflict/ext-language_tools.js';
import 'ace-builds/src-min-noconflict/keybinding-emacs.js';
import 'ace-builds/src-min-noconflict/keybinding-vim.js';
import 'ace-builds/src-min-noconflict/theme-chrome.js';
import 'node-blockly/browser';

import './grammar.ne';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
global.monaco = monaco;

import './src/Main.purs';
