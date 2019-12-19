'use strict';

const ExtractTextPlugin = require("extract-text-webpack-plugin");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const path = require('path');
const webpack = require('webpack');
const fs = require('fs');

const isWebpackDevServer = process.argv.some(a => path.basename(a) === 'webpack-dev-server');

const isWatch = process.argv.some(a => a === '--watch');

const plugins =
    isWebpackDevServer || !isWatch ? [] : [
        function () {
            this.plugin('done', function (stats) {
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
        // hot: false,
        https: true,
        writeToDisk: true,
        proxy: {
            "/api": {
                target: 'http://localhost:8080'
            }
        }
    },

    entry: { main: './entry.js', worker: './worker.js' },

    output: {
        path: path.join(__dirname, 'dist'),
        pathinfo: true,
        filename: '[name].[hash].js'
    },

    node: {
        fs: "empty"
    },

    module: {
        rules: [
            { test: /\.woff(2)?(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "url-loader?limit=10000&mimetype=application/font-woff" },
            { test: /fontawesome-.*\.(ttf|eot|svg)(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "file-loader" },
            {
                test: /\.purs$/,
                exclude: /src/,
                use: [
                    {
                        loader: 'purs-loader',
                        options: {
                            src: [
                                'worker/**/*.purs',
                                '.spago/*/*/src/**/*.purs'
                            ],
                            spago: true,
                            psc: null,
                            // TODO: https://github.com/ethul/purs-loader/issues/139
                            // bundle: !(isWebpackDevServer || isWatch),
                            bundle: true,
                            warnings: true,
                            watch: isWebpackDevServer || isWatch,
                            pscPackage: false,
                            pscIde: false
                        }
                    }
                ]
            },
            {
                test: /\.purs$/,
                exclude: /worker/,
                use: [
                    {
                        loader: 'purs-loader',
                        options: {
                            src: [
                                'src/**/*.purs',
                                'generated/**/*.purs',
                                '.spago/*/*/src/**/*.purs',
                                '../web-common/src/**/*.purs'
                            ],
                            spago: true,
                            psc: null,
                            // TODO: https://github.com/ethul/purs-loader/issues/139
                            // bundle: !(isWebpackDevServer || isWatch),
                            bundle: true,
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
            },
            {
                test: /z3w\.js$/,
                loader: "exports-loader"
            },
            {
                test: /z3w\.wasm$/,
                type: "javascript/auto",
                loader: "file-loader"
            }
        ]
    },

    resolve: {
        modules: [
            'node_modules', '.'
        ],
        extensions: ['.purs', '.js']
    },

    plugins: [
        new webpack.LoaderOptionsPlugin({
            debug: true
        }),
        new HtmlWebpackPlugin({
            template: '../web-common/static/index.html',
            favicon: 'static/favicon.ico',
            title: 'Marlowe Playground',
            productName: 'marlowe-playground',
            chunks: ['main'],
            googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-119953429-7'
        }),
        new webpack.NormalModuleReplacementPlugin(/^echarts$/, 'echarts/dist/echarts.min.js'),

        function (compiler) {
            compiler.hooks.done.tap('ReplaceWithHash', (stats) => {
                var replaceInFile = function (filePath, toReplace, replacement) {
                    logger.info("replace " + toReplace + " with " + replacement + " in " + filePath);
                    var replacer = function (match) {
                        logger.info('Replacing in %s: %s => %s', filePath, match, replacement);
                        return replacement
                    };
                    try {
                        var str = compiler.inputFileSystem.readFileSync(filePath, 'utf8').toString();
                        var out = str.replace(toReplace, replacer);
                        compiler.outputFileSystem.writeFile(filePath, out, (err) => {
                            logger.info("wrote file");
                            if (err) {
                                logger.error("failed to write file: " + err);
                            }
                        });
                    } catch (error) {
                        // ignore file not found
                        logger.error("couldn't replace file" + filePath);
                        logger.error(error);
                    }
                };

                var hash = stats.hash; // Build's hash, found in `stats` since build lifecycle is done.
                var logger = compiler.getInfrastructureLogger('ReplaceWithHash');
                replaceInFile(path.join(compiler.outputPath, 'main.' + hash + '.js'),
                    /worker.\[hash\].js/g,
                    'worker.' + hash + '.js'
                );
            });
        }
    ].concat(plugins)
};
