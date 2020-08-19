{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Int (Int32)
import qualified Language.R as R
import Language.R (R)
import Language.R.QQ

r_shiny :: R s Int32
r_shiny = do
    R.dynSEXP <$> [r| 
        library(shiny)

        ui <- fluidPage(

            titlePanel("Hello Shiny!"),

            sidebarLayout(
                sidebarPanel(

                    sliderInput(inputId = "bins",
                                label = "Number of bins:",
                                min = 1,
                                max = 50,
                                value = 30)

                    ),
                mainPanel(
                    plotOutput(outputId = "distPlot")
                )
            )
        )

        server <- function(input, output) {

            output$distPlot <- renderPlot({

                x    <- faithful$waiting
                bins <- seq(min(x), max(x), length.out = input$bins + 1)

                hist(x, breaks = bins, col = "#75AADB", border = "white",
                    xlab = "Waiting time to next eruption (in mins)",
                    main = "Histogram of waiting times")

            })

        }

        # Create Shiny app ----
        message("Starting Marlowe Shiny app")
        runApp(shinyApp(ui = ui, server = server), port = 8081)
        1
    |]

main :: IO ()
main = R.withEmbeddedR R.defaultConfig $ do
    code <- R.runRegion $ r_shiny
    print code