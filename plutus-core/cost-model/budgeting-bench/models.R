library(dplyr)
library(stringr)
library(MASS)
library(broom)

# See Note [Creation of the Cost Model]

benchData <- function(path) {

  dat <- read.csv(
    path,
    header=TRUE,
    stringsAsFactors=FALSE
  )

  benchname <- regex("([:alnum:]+)/ExMemory (\\d+)(?:/ExMemory (\\d+)?)?")

  numbercols = c("x_mem", "y_mem")

  benchmark_name_to_numbers <- function(name) {
    res <- as.data.frame(
      str_match(name, benchname)
    )
    names(res) <- c("Name2", "BuiltinName", numbercols)
    res
  }

  numbers <- benchmark_name_to_numbers(dat$Name)

  mutated <- numbers %>% mutate_at(numbercols, function(x) { as.numeric(as.character(x))}) %>% mutate_at(c("BuiltinName"), as.character)
  cbind(dat, mutated) %>%
    mutate_at(c("Mean", "MeanLB", "MeanUB", "Stddev", "StddevLB", "StddevUB"), function(x) { x * 1000 * 1000 })
}

# path <- "plutus-core/budgeting-bench/csvs/benching.csv"

modelFun <- function(path) {
  data <- benchData(path)

  calibratingBenchModel <- {
    # CalibratingBench is number of runs as ExMemory, because I'm too lazy to write a new parser.
    filtered <- data %>% filter(BuiltinName == "CalibratingBench")
    lm(Mean ~ x_mem, data=filtered)
  }

  baseCost <- calibratingBenchModel$coefficients[["(Intercept)"]]
  data$Mean <- data$Mean - baseCost

  # filtered does leak from one model to the next, so make sure you don't mistype!

  addIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "AddInteger") %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(x_mem + y_mem), filtered)
  }

  eqIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "EqInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }

  subtractIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "SubtractInteger") %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(x_mem + y_mem), filtered)
  }

  multiplyIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "MultiplyInteger") %>% filter(x_mem != 0) %>% filter(y_mem != 0) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(x_mem * y_mem), filtered)
  }

  divideIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "DivideInteger") %>% filter(x_mem != 0) %>% filter(y_mem != 0) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    # This one does seem to underestimate the cost by a factor of two
    lm(Mean ~ ifelse(x_mem > y_mem, I(x_mem * y_mem), 0) , filtered)
  }
  quotientIntegerModel <- divideIntegerModel
  remainderIntegerModel <- divideIntegerModel
  modIntegerModel <- divideIntegerModel

  lessThanIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "LessThanInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }
  greaterThanIntegerModel <- lessThanIntegerModel

  lessThanEqIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "LessThanEqInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }
  greaterThanEqIntegerModel <- lessThanEqIntegerModel

  eqByteStringModel <- {
    filtered <- data %>% filter(BuiltinName == "EqByteString") %>% filter(x_mem == y_mem)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }

  ltByteStringModel <- {
    filtered <- data %>% filter(BuiltinName == "LtByteString")
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }
  gtByteStringModel <- ltByteStringModel

  concatenateModel <- {
    filtered <- data %>% filter(BuiltinName == "Concatenate") %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
    lm(Mean ~ I(x_mem + y_mem), data=filtered)
  }

  takeByteStringModel <- {
    filtered <- data %>% filter(BuiltinName == "TakeByteString")
    lm(Mean ~ 1, data=filtered)
  }
  dropByteStringModel <- {
    filtered <- data %>% filter(BuiltinName == "DropByteString")
    lm(Mean ~ 1, data=filtered)
  }

  sHA2Model <- {
    filtered <- data %>% filter(BuiltinName == "SHA2")
    lm(Mean ~ x_mem, data=filtered)
  }
  sHA3Model <- {
    filtered <- data %>% filter(BuiltinName == "SHA3")
    lm(Mean ~ x_mem, data=filtered)
  }
  verifySignatureModel <- {
    filtered <- data %>% filter(BuiltinName == "VerifySignature")
    lm(Mean ~ 1, data=filtered)
  }

  ifThenElseModel <- 0

  list(
    addIntegerModel=addIntegerModel,
    eqIntegerModel=eqIntegerModel,
    subtractIntegerModel=subtractIntegerModel,
    multiplyIntegerModel=multiplyIntegerModel,
    divideIntegerModel=divideIntegerModel,
    quotientIntegerModel=quotientIntegerModel,
    remainderIntegerModel=remainderIntegerModel,
    modIntegerModel=modIntegerModel,
    lessThanIntegerModel=lessThanIntegerModel,
    greaterThanIntegerModel=greaterThanIntegerModel,
    lessThanEqIntegerModel=lessThanEqIntegerModel,
    greaterThanEqIntegerModel=greaterThanEqIntegerModel,
    concatenateModel=concatenateModel,
    takeByteStringModel=takeByteStringModel,
    dropByteStringModel=dropByteStringModel,
    sHA2Model=sHA2Model,
    sHA3Model=sHA3Model,
    verifySignatureModel=verifySignatureModel,
    eqByteStringModel=eqByteStringModel,
    ltByteStringModel=ltByteStringModel,
    gtByteStringModel=gtByteStringModel,
    ifThenElseModel=ifThenElseModel
  )

}
