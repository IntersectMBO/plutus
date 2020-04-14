import '@fortawesome/fontawesome-free/css/all.css';
import './static/css/main.scss';
import 'node-blockly/browser';

import './grammar.ne';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
global.monaco = monaco;

import './src/Main.purs';
