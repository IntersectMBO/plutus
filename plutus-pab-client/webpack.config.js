'use strict';

const ExtractTextPlugin = require("extract-text-webpack-plugin");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const path = require('path');
const webpack = require('webpack');

const isWebpackDevServer = process.argv.some(a => path.basename(a) === 'webpack-dev-server');

const isWatch = process.argv.some(a => a === '--watch');

const plugins =
      isWebpackDevServer || !isWatch ? [] : [
          function(){
              this.plugin('done', function(stats){
                  process.stderr.write(stats.toString('errors-only'));
              });
          }
      ]
;

// source map adds many Mb to the output!
const devtool = isWebpackDevServer ? 'eval-source-map' : false;

module.exports = {
    devtool,

    devServer: {
        contentBase: path.join(__dirname, "dist"),
        compress: true,
        port: 8009,
        https: true,
        proxy: {
            "/api": {
                target: 'http://localhost:9080'
            },
            "/ws": {
                target: 'ws://localhost:9080',
                ws: true,
                onError(err) {
                  console.log('Error with the WebSocket:', err);
                }
            }
        }
    },

    entry: './entry.js',

    output: {
        path: path.join(__dirname, 'dist'),
        pathinfo: true,
        filename: 'app.[hash].js'
    },

    module: {
        rules: [
            { test: /\.woff(2)?(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "url-loader?limit=10000&mimetype=application/font-woff" },
            { test: /fontawesome-.*\.(ttf|eot|svg)(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "file-loader" },
            {
                test: /\.purs$/,
                use: [
                    {
                        loader: 'purs-loader',
                        options: {
                            src: [
                                'src/**/*.purs',
                                'generated/**/*.purs',
                                '.spago/*/*/src/**/*.purs',
                                'web-common-plutus/**/*.purs',
                                'web-common/**/*.purs'
                            ],
                            psc: null,
                            bundle: !(isWebpackDevServer || isWatch),
                            warnings: true,
                            watch: isWebpackDevServer || isWatch,
                            pscPackage: false,
                            pscIde: false
                        }
                    }
                ]
            },
            {
                test: /\.css$/,
                use: ['style-loader', 'css-loader']
            },
            {
                test: /\.scss$/,
                use: ['style-loader', 'css-loader', 'sass-loader']
            },
            {
                test: /\.(gif|png|jpe?g|svg)$/i,
                use: 'url-loader'
            }
        ]
    },

    resolve: {
        modules: [
            // We need the second entry for node to be able to
            // locate `node_modules` from client directory when 
            // modules are referenced from inside `web-common`.
            'node_modules', path.resolve(__dirname, './node_modules')
        ],
        extensions: [ '.purs', '.js']
    },

    plugins: [
        new webpack.LoaderOptionsPlugin({
            debug: true
        }),
        new HtmlWebpackPlugin({
            template: 'static/index.html',
            favicon: 'static/favicon.ico',
            title: 'SCB',
            productName: 'plutus-pab'
        })
    ].concat(plugins)
};
