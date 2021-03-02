'use strict';

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
            "/ws": {
                target: 'ws://localhost:8080',
                ws: true
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
                                'web-common-marlowe/**/*.purs',
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
            }, {
                test: /\.tsx?$/,
                loader: "ts-loader"
            },
            {
                test: /\.css$/,
                exclude: /node_modules/,
                use: ['style-loader', 'css-loader', 'postcss-loader']
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
            title: 'Marlowe Marketplace',
            productName: 'marlowe-marketplace',
            // FIXME: We need to get a google analytics id
            googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-FIX-ME'
        })
    ].concat(plugins)
};
