'use strict';

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
        contentBase: '.',
        port: 4008,
        stats: 'errors-only'
    },

    entry: './entry.js',

    output: {
        path: __dirname,
        pathinfo: true,
        filename: 'bundle.js'
    },

    module: {
        rules: [
            { test: /\.woff(2)?(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "url-loader?limit=10000&mimetype=application/font-woff" },
            { test: /\.(ttf|eot|svg)(\?v=[0-9]\.[0-9]\.[0-9])?$/, loader: "file-loader" },
            {
                test: /\.purs$/,
                use: [
                    {
                        loader: 'purs-loader',
                        options: {
                            src: [
                                'bower_components/purescript-*/src/**/*.purs',
                                'src/**/*.purs'
                            ],
                            bundle: false,
                            psc: 'psa',
                            watch: isWebpackDevServer || isWatch,
                            pscIde: true
                        }
                    }
                ]
            },
            {
                test: /\.css$/,
                use: ['style-loader', 'css-loader']
            },
            {
                test: /\.less$/,
        use: [{
          loader: "style-loader" // creates style nodes from JS strings
        }, {
          loader: "css-loader" // translates CSS into CommonJS
        }, {
          loader: "less-loader" // compiles Less to CSS
        }]
            }
        ]
    },

    resolve: {
        modules: [ 'node_modules', 'bower_components', 'static' ],
        extensions: [ '.purs', '.js', '.less']
    },

    plugins: [
        new webpack.LoaderOptionsPlugin({
            debug: true
        })
    ].concat(plugins)
};
