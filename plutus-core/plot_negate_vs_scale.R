#!/usr/bin/env Rscript

# This is ai code

args <- commandArgs(trailingOnly = TRUE)
csv_path <- if (length(args) > 0) args[[1]] else "negatevsscalevalue-betternegate-test.csv"
default_png <- paste0(tools::file_path_sans_ext(csv_path), ".png")
output_path <- if (length(args) > 1) args[[2]] else default_png

data <- read.csv(
  csv_path,
  comment.char = "#",
  stringsAsFactors = FALSE
)

data$group <- ifelse(
  grepl("^NegateValue/", data$benchmark),
  "NegateValue",
  ifelse(grepl("^ScaleValue/1/", data$benchmark), "ScaleValue", NA_character_)
)

plot_data <- subset(data, !is.na(group))

if (nrow(plot_data) == 0) {
  stop("No NegateValue or ScaleValue rows were found in ", csv_path)
}

plot_data$x <- as.numeric(sub("^.*?/(\\d+)$", "\\1", plot_data$benchmark))

if (anyNA(plot_data$x)) {
  stop("Failed to extract the numeric suffix from at least one benchmark name.")
}

negate_color <- "#1f77b4"
scale_color <- "#d62728"

png(
  filename = output_path,
  width = 1600,
  height = 900,
  res = 120
)

plot(
  range(plot_data$x),
  range(plot_data$t),
  type = "n",
  xlab = "Value Size",
  ylab = "t",
  main = "NegateValue vs ScaleValue"
)

with(
  subset(plot_data, group == "NegateValue"),
  points(x, t, col = negate_color, pch = 16)
)

with(
  subset(plot_data, group == "ScaleValue"),
  points(x, t, col = scale_color, pch = 16)
)

legend(
  "topright",
  legend = c("NegateValue", "ScaleValue"),
  col = c(negate_color, scale_color),
  pch = 16,
  bty = "n"
)

dev.off()
message("Plot saved to ", output_path)
