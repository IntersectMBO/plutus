const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const MiniCssExtractPlugin = require("mini-css-extract-plugin");
const faqContent = require("./faqContent.json");

const isDevelopment = process.env.NODE_ENV === "development";

const googleAnalyticsId = isDevelopment ? "UA-XXXXXXXXX-X" : "G-E6DSPBDB87";
const segmentAnalyticsId = isDevelopment ? "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX" : "eKDUP7DVpmHzpqvvwuO5GXpfXmyAI6Y4";

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
    hot: false,
    liveReload: true,
    overlay: true,
    writeToDisk: true,
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
        test: /\.njk$/,
        use: [
          {
            loader: "simple-nunjucks-loader",
            options: {},
          },
        ],
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
  stats: {
    logging: "info",
  },

  plugins: [
    new HtmlWebpackPlugin({
      template: path.resolve(__dirname, "src/index.njk"),
      templateParameters: { faqContent, googleAnalyticsId, segmentAnalyticsId },
      favicon: "static/favicon.ico",
      title: "Marlowe",
    }),
    new MiniCssExtractPlugin({
      filename: "css/[name]-[chunkhash].css",
    }),
  ],
};
