"use strict";

const path = require("path");
const nodeExternals = require("webpack-node-externals");

module.exports = {
    target: "node",
    externals: [nodeExternals()],
    optimization: {
        minimize: false,
    },
    entry: "./test/entry.js",
    output: {
        path: path.join(__dirname, "dist"),
        pathinfo: true,
        filename: "test.js"
    },
    module: {
        rules: [
            {
                test: /\.ne$/,
                loader: "nearley-webpack-loader",
                options: {
                    baseDir: "."
                }
            }, {
                test: /\.tsx?$/,
                loader: "ts-loader"
            },
            {
                test: /\.purs$/,
                use: [
                    {
                        loader: "purs-loader",
                        options: {
                            src: [
                                "src/**/*.purs",
                                "generated/**/*.purs",
                                ".spago/*/*/src/**/*.purs",
                                "web-common/**/*.purs",
                                "web-common-marlowe/**/*.purs",
                                "web-common-playground/**/*.purs",
                                "test/**/*.purs"
                            ],
                        }
                    }
                ]
            },
            {
                test: /\.(gif|png|jpe?g|svg)$/i,
                use: "url-loader"
            },
        ]
    },
    resolve: {
        modules: [
            // We need the second entry for node to be able to
            // locate `node_modules` from client directory when 
            // modules are referenced from inside `web-common`.
            "node_modules", path.resolve(__dirname, "./node_modules")
        ],
        alias: {
            grammar: path.resolve(__dirname, "./grammar.ne"),
            static: path.resolve(__dirname, "./static"),
            src: path.resolve(__dirname, "./src")
        },
        extensions: [".purs", ".js", ".ts"]
    },
    resolveLoader: {
        modules: [
            "node_modules",
            path.resolve(__dirname, ".")
        ]
    },
};
