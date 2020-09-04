{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Int (Int32)
import qualified Language.R as R
import Language.R (R)
import Language.R.QQ
import Language.Marlowe.ACTUS.Analysis(genProjectedCashflows)
import Data.Time.Calendar(showGregorian, fromGregorian)
import Language.Marlowe.ACTUS.Definitions.ContractTerms
import Language.Marlowe.ACTUS.Definitions.Schedule(CashFlow(..))
import Data.Aeson(encode, decode)
import Data.String (IsString (fromString))
import Data.ByteString.Lazy.Char8(unpack)

get_dates :: String -> R s [String]
get_dates ct = return $ case (decode $ fromString ct) of
    Just ct' -> showGregorian <$> cashCalculationDay <$> genProjectedCashflows ct'
    Nothing -> []

get_cfs :: String -> R s [Double]
get_cfs ct = return $ case (decode $ fromString ct) of
    Just ct' -> amount <$> genProjectedCashflows ct'
    Nothing -> []

r_shiny :: R s Int32
r_shiny = do
    R.dynSEXP <$> [r| 
library(shiny)
library(shinyjs)
library(plotly)
library(purrr)

jscode <- "
shinyjs.init = function() {
  window.addEventListener(\"message\", receiveMessage, false);

  function receiveMessage(event) {
    Shiny.onInputChange(\"contract\", event.data); 
  }
}"

ui <- fluidPage(
  useShinyjs(),
  extendShinyjs(text = jscode, functions = c()),  
  headerPanel(''),
  mainPanel(
    plotlyOutput('plot')
  )
)

server <- function(input, output) {
  observeEvent(input$contract, {
    message(paste("Contract: ", input$contract))
    x <- get_dates_hs(input$contract)
    y <- get_cfs_hs(input$contract)
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
  })
  
}

# Create Shiny app ----
message("Starting Marlowe Shiny app: ")
runApp(shinyApp(ui = ui, server = server), port = 8081)
1
    |]

main :: IO ()
main = R.withEmbeddedR R.defaultConfig $ do
    code <- R.runRegion $ r_shiny
    print code


contractTermsJson :: String
contractTermsJson = unpack $ encode contractTerms

contractTerms :: ContractTerms
contractTerms = ContractTerms {
          contractId = "0"
        , contractType = PAM
        , ct_IED = fromGregorian 2008 10 20 -- Initial Exchange Date
        , ct_SD = fromGregorian 2008 10 22 -- start date
        , ct_MD = fromGregorian 2009 10 22 -- maturity date
        , ct_TD = fromGregorian 2009 10 22  -- termination date
        , ct_PRD = fromGregorian 2008 10 20 -- purchase date
        , ct_CNTRL = CR_ST
        , ct_PDIED = -100.0 -- Discount At IED
        , ct_NT = 1000.0 -- Notional
        , ct_PPRD = 1200.0 -- Price At Purchase Date
        , ct_PTD = 1200.0 -- Price At Termination Date
        , ct_DCC = DCC_A_360 -- Date Count Convention
        , ct_PREF = PREF_Y -- allow PP
        , ct_PRF = CS_PF
        , scfg = ScheduleConfig {
            calendar = []
            , includeEndDay = False
            , eomc = EOMC_EOM
            , bdc = BDC_NULL
        }
        -- Penalties
        , ct_PYRT = 0.0
        , ct_PYTP = PYTP_A -- Penalty Pype
        , ct_cPYRT = 0.0
        -- Optionality
        , ct_OPCL = Nothing
        , ct_OPANX = Nothing
        -- Scaling:
        , ct_SCIED = 0.0
        , ct_SCEF = SE_000
        , ct_SCCL = Nothing
        , ct_SCANX = Nothing
        , ct_SCIXSD = 0.0
        -- Rate Reset
        , ct_RRCL = Nothing
        , ct_RRANX = Nothing
        , ct_RRNXT = Nothing
        , ct_RRSP = 0.0
        , ct_RRMLT = 0.0
        , ct_RRPF = 0.0
        , ct_RRPC = 0.0
        , ct_RRLC = 0.0
        , ct_RRLF = 0.0
        -- Interest
        , ct_IPCED = Nothing
        , ct_IPCL  = Nothing
        , ct_IPANX = Nothing
        , ct_IPNR  = Nothing
        , ct_IPAC  = Nothing
        -- Fee
        , ct_FECL  = Nothing
        , ct_FEANX  = Nothing
        , ct_FEAC  = Nothing
        , ct_FEB = FEB_N
        , ct_FER = 0.03 -- fee rate
        , ct_CURS = False
        , constraints = Nothing
    }