const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const MiniCssExtractPlugin = require("mini-css-extract-plugin");
module.exports = {
  entry: path.resolve(__dirname, "src/index.js"),
  output: {
    filename: "js/main-[chunkhash].js",
    path: path.resolve(__dirname, "public"),
    publicPath: "/",
    clean: true,
  },
  devServer: {
    port: 8000,
    compress: true,
    contentBase: path.resolve(__dirname, "public"),
  },
  module: {
    rules: [
      {
        test: /\.css$/i,
        use: [MiniCssExtractPlugin.loader, "css-loader", "postcss-loader"],
      },
      {
        test: /\.(woff|woff2|eot|ttf|otf)$/i,
        type: "asset/resource",
      },
      {
        test: /\.(gif|png|jpe?g|svg)$/i,
        type: "asset/resource",
        generator: {
          filename: "img/[hash][ext][query]",
        },
      },
    ],
  },
  target: "web",
  plugins: [
    new HtmlWebpackPlugin({
      template: path.resolve(__dirname, "src/index.html"),
      // favicon: 'static/favicon.ico',
      title: "Marlowe",
      liveReload: true,
      // FIXME: add google analytics id
      // googleAnalyticsId: isWebpackDevServer ? 'UA-XXXXXXXXX-X' : 'UA-119953429-16'
    }),
    new MiniCssExtractPlugin({
      filename: "css/[name]-[chunkhash].css",
    }),
  ],
};
