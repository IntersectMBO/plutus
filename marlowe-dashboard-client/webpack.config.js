"use strict";

const HtmlWebpackPlugin = require("html-webpack-plugin");
const MiniCssExtractPlugin = require("mini-css-extract-plugin");
const path = require("path");

const isDevelopment = process.env.NODE_ENV === "development";

const devtool = isDevelopment ? "eval-source-map" : false;

module.exports = {
    devtool,
    devServer: {
        contentBase: path.join(__dirname, "dist"),
        compress: true,
        port: 8009,
        https: true,
        stats: "errors-warnings",
        proxy: {
            "/api": {
                target: "http://localhost:9080",
            },
            "/wallet": {
                target: "http://localhost:9080",
            },
            "/ws": {
                target: "ws://localhost:9080",
                ws: true,
                onError (err) {
                  console.log("Error with the WebSocket:", err);
                },
            },
        },
    },
    entry: "./entry.js",
    output: {
        filename: "[name].[contenthash].js",
        path: path.join(__dirname, "dist"),
        pathinfo: true,
        clean: true,
    },
    optimization: {
        runtimeChunk: "single",
        splitChunks: {
            cacheGroups: {
                vendor: {
                    test: /[\\/]node_modules[\\/]/,
                    name: "vendors",
                    chunks: "all",
                },
            },
        },
    },
    module: {
        rules: [
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
                                "web-common-marlowe/**/*.purs",
                                "web-common/**/*.purs",
                            ],
                            psc: "psa",
                            bundle: !isDevelopment,
                            watch: isDevelopment,
                        },
                    },
                ],
            },
            {
                test: /\.css$/,
                exclude: /node_modules/,
                use: [MiniCssExtractPlugin.loader, "css-loader", "postcss-loader"],
            },
            {
                test: /\.(png|svg|jpg|jpeg|gif)$/i,
                type: "asset/resource",
            },
            {
                test: /\.(woff|woff2|eot|ttf|otf)$/i,
                type: "asset/resource",
            },
        ],
    },
    resolve: {
        modules: [
            "node_modules",
            // We need this entry for node to be able to locate `node_modules` from
            // client directory when modules are referenced from inside `web-common`.
            path.resolve(__dirname, "./node_modules"),
        ],
        alias: {
            contracts: path.resolve(__dirname, "./contracts"),
            static: path.resolve(__dirname, "./static"),
            src: path.resolve(__dirname, "./src"),
        },
        extensions: [".purs", ".js"],
    },
    resolveLoader: {
        modules: [
            "node_modules",
            path.resolve(__dirname, "."),
        ],
    },
    plugins: [
        new HtmlWebpackPlugin({
            template: "./static/index.html",
            favicon: "static/favicon.ico",
            title: "Marlowe Run",
            productName: "marlowe-run",
            googleAnalyticsId: isDevelopment ? "UA-XXXXXXXXX-X" : "UA-119953429-16",
        }),
        new MiniCssExtractPlugin({
            filename: "[name].[contenthash].css",
        }),
    ],
};
