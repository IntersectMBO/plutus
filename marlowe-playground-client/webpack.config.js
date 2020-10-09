'use strict';

const MonacoWebpackPlugin = require('monaco-editor-webpack-plugin');
const HtmlWebpackPlugin = require('html-webpack-plugin');
const path = require('path');

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

// source map adds 20Mb to the output!
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
                target: 'http://localhost:8080'
            },
            "/runghc": {
                target: 'http://localhost:8080'
            },
            "/marlowe-analysis": {
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
                test: /\.ne$/,
                loader: 'nearley-webpack-loader',
                options: {
                    baseDir: '.'
                }
            },
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
                                '../web-common/**/*.purs'
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
            }, {
                test: /\.tsx?$/,
                loader: "ts-loader"
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
                test: /\.ttf$/,
                use: ['file-loader'],
            }
        ]
    },

    resolve: {
        modules: [
            'node_modules'
        ],
        alias: {
            grammar: path.resolve(__dirname, './grammar.ne'),
            static: path.resolve(__dirname, './static'),
            src: path.resolve(__dirname, './src')
        },
        extensions: ['.purs', '.js', '.ts', '.tsx']
    },

    resolveLoader: {
        modules: [
            'node_modules',
            path.resolve(__dirname, '.')
        ]
    },

    plugins: [
        new HtmlWebpackPlugin({
            template: './static/index.html',
            favicon: 'static/favicon.ico',
            title: 'Marlowe Playground',
            productName: 'marlowe-playground',
            googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-119953429-16'
        }),
        new MonacoWebpackPlugin({
            // note that you have to include typescript if you want javascript to work!
            languages: ['javascript', 'typescript'],
        })
    ].concat(plugins)
};
