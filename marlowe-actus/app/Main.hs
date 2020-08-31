{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Int (Int32)
import qualified Language.R as R
import Language.R (R)
import Language.R.QQ


get_dates :: String -> R s [String]
get_dates ct = return ["01-01-2020", "01-01-2021", "01-01-2022", "01-01-2023", "01-01-2024", "01-01-2025"]

get_cfs :: String -> R s [Int32]
get_cfs ct = return [-120, 60, 80, 5, -40, -20]

r_shiny :: R s Int32
r_shiny = do
    R.dynSEXP <$> [r| 
library(shiny)
library(plotly)
library(purrr)

ui <- fluidPage(
  headerPanel(''),
  mainPanel(
    plotlyOutput('plot')
  )
)

server <- function(input, output) {
  
  x <- get_dates_hs("")
  y <- get_cfs_hs("")
  text <- y %>% 
    map(function(x) if (x > 0) paste("+", toString(x), sep = "") else toString(x))
  data <- data.frame(x=factor(x,levels=x),text,y)

  fig <- plot_ly(
    data, name = "20", type = "waterfall",
    x = ~x, textposition = "outside", y= ~y, text =~text,
    connector = list(line = list(color= "rgb(63, 63, 63)"))) 
  fig <- fig %>% layout(title = "Cashflows",
          xaxis = list(title = ""),
          yaxis = list(title = ""),
          autosize = TRUE)

  fig
  output$plot <- renderPlotly(fig)

}

shinyApp(ui,server)

# Create Shiny app ----
message("Starting Marlowe Shiny app")
runApp(shinyApp(ui = ui, server = server), port = 8081)
1
    |]

main :: IO ()
main = R.withEmbeddedR R.defaultConfig $ do
    code <- R.runRegion $ r_shiny
    print code