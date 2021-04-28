const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const MiniCssExtractPlugin = require('mini-css-extract-plugin');

module.exports = {
  entry: "./src/index.js",
  output: {
    filename: "./js/main-[hash].js",
    path: path.resolve(__dirname, "public"),
  },
  devServer: {
    port: 8000,
    compress: true,
    contentBase: path.join(__dirname, "public"),
  },
  module: {
    rules: [
      {
        test: /\.css$/i,
        use: [MiniCssExtractPlugin.loader, 'css-loader', 'postcss-loader']
      },
    ],
  },
  target: "web",
  plugins: [
    new HtmlWebpackPlugin({
      template: "./src/index.html",
      // favicon: 'static/favicon.ico',
      title: "Marlowe",
      liveReload: true
      // FIXME: add google analytics id
      // googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-119953429-16'
    }),
    new MiniCssExtractPlugin({
      filename: "css/[name]-[hash].css"
    })
  ],
};
