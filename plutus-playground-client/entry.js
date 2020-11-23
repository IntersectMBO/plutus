import '@fortawesome/fontawesome-free/css/all.css';
import 'chartist/dist/chartist.min.css';
import 'chartist/dist/chartist.min.js';
import 'chartist-plugin-tooltips/dist/chartist-plugin-tooltip.css';
import 'chartist-plugin-tooltips/dist/chartist-plugin-tooltip.min.js';
import 'chartist-plugin-axistitle/dist/chartist-plugin-axistitle.min.js';
import './static/main.scss';

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api';
global.monaco = monaco;
import { EmacsExtension } from 'monaco-emacs';
global.EmacsExtension = EmacsExtension;
import { initVimMode } from 'monaco-vim';
global.initVimMode = initVimMode;
global.monacoExtraTypeScriptLibs = [];

import './src/Main.purs';
