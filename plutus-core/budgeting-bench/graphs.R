# See CostModel.md, #Add a new kind of model
library(plotly)
# install.packages("plotly")

# this one is @reactormonk specific
# options(browser="$HOME/browser.bash")
# options(error=traceback)

plotRaw <- function(filtered) {
  plot_ly(filtered, x=filtered$x_mem, y=filtered$y_mem, z=filtered$Mean) %>%
    add_trace(
        type="scatter3d"
      , mode="markers"
      , size=2
      ) %>% layout(
        scene=list(
          xaxis=list(title=list(text="ExMemory of first argument"))
        , yaxis=list(title=list(text="ExMemory of second argument"))
        #   xaxis=list(title=list(text="ExMemory of first argument"), type="log")
        # , yaxis=list(title=list(text="ExMemory of second argument"), type="log")
        , zaxis=list(title=list(text="Time of operation"))
        , camera = list(eye = list(x = -1, y = -2, z = 0.5))
        )
      )
  # add_trace(type="scatter3d", mode="markers", name="measured")
}

plotRaw2d <- function(filtered) {
  plot_ly(filtered, x=filtered$x_mem, y=filtered$Mean) %>%
    add_trace(
        type = "scatter"
      , mode="markers"
      , size=2
      ) %>% layout(
        xaxis=list(title=list(text="ExMemory of first argument"))
      , yaxis=list(title=list(text="Time of operation"))
      )
}

plotErrorModel <- function(filtered, filteredModel) {
  filtered$predicted <- predict(filteredModel, newdata = filtered)

  errors <- filtered$Mean - filtered$predicted
  positiveErrors <- pmax(errors, 0)
  negativeErrors <- lapply(pmin(errors,0), abs)
  plot_ly(filtered, x=filtered$x_mem, y=filtered$y_mem, z=filtered$predicte) %>%
    add_trace(
        type="scatter3d"
      , mode="markers"
      , name="Predicted"
      , marker=list(size=2)
      , error_z=list(type="data", array=positiveErrors, arrayminus=negativeErrors, symmetric=FALSE)
      , error_z=list(type="constant", value=0.05, symmetric=FALSE)
      ) %>% layout(
        scene=list(
          xaxis=list(title=list(text="ExMemory of first argument"))
        , yaxis=list(title=list(text="ExMemory of second argument"))
        , zaxis=list(title=list(text="Time of operation"))
        , camera = list(eye = list(x = -1, y = -2, z = 0.5))
        )
      ) %>%
      add_trace(type="scatter3d", mode="markers", name="Measured", marker=list(colour="black", size=2), z=filtered$Mean)
}

# x_mempos <- unique(ai$x_mem)
# y_mempos <- unique(ai$y_mem)
# grid <- with(ai, expand.grid(x_mempos, y_mempos))
# predicting_df <- setNames(data.frame(grid), c("x_mem", "y_mem"))
# m <- matrix(predicted, nrow=length(unique(predicting_df$x_mem)), ncol=length(unique(predicting_df$y_mem)))

filtered <- data %>% filter(BuiltinName == "DropByteString")
plotRaw(filtered)
plotRaw2d(filtered)

plotErrorModel(filtered, concatenateModel)

# tidy(model)
# summary(model)

# ggplot(addInt, aes(x=I(x_log2 + y_log2), y=Mean)) +
#   facet_wrap(~BuiltinName) +
#   geom_line() +
#   geom_smooth(method="lm")

# ggplot(addInt, aes(x=x_log2, y=y_log2, z=Mean)) +
#   geom_contour(aes(colour=stat(level)), bins=30) +
#   facet_wrap(vars(BuiltinName))

# ggsave("plot.png")

# unique(benchData$BuiltinName)
