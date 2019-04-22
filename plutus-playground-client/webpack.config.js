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

module.exports = {
    devtool: 'eval-source-map',

    devServer: {
        contentBase: path.join(__dirname, "dist"),
        compress: true,
        port: 8009,
        https: true,
        proxy: {
            "/api": {
                target: 'http://localhost:8080'
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
                                'bower_components/purescript-*/src/**/*.purs',
                                'src/**/*.purs',
                                'generated/**/*.purs',
                                '../web-common/src/**/*.purs'
                            ],
                            psc: 'psa',
                            bundle: !(isWebpackDevServer || isWatch),
                            watch: isWebpackDevServer || isWatch,
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
            'node_modules',
            'bower_components'
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
            googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-119953429-7'
        }),
        new webpack.NormalModuleReplacementPlugin(/^echarts$/, 'echarts/dist/echarts.min.js')
    ].concat(plugins)
};
