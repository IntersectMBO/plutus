import '@fortawesome/fontawesome-free/css/all.css';
import './static/css/main.scss';
import 'node-blockly/browser';

import './grammar.ne';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
global.monaco = monaco;
import { EmacsExtension } from 'monaco-emacs';
global.EmacsExtension = EmacsExtension;
import { initVimMode } from 'monaco-vim';
global.initVimMode = initVimMode;

import './src/Main.purs';
