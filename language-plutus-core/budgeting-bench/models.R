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

  benchname <- regex("(\\w+)/ExMemory (\\d+)/ExMemory (\\d+)")

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
  cbind(dat, mutated) %>% filter(x_mem < 2000) %>% filter(y_mem < 2000)
}

# path <- "language-plutus-core/budgeting-bench/csvs/benching.csv"

modelFun <- function(path) {
  data <- benchData(path)
  # filtered does leak from one model to the next, so make sure you don't mistype!

  addIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "AddInteger")
    lm(Mean ~ I(x_mem + y_mem), filtered)
  }

  eqIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "EqInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }

  subtractIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "SubtractInteger")
    lm(Mean ~ I(x_mem + y_mem), filtered)
  }

  multiplyIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "MultiplyInteger") %>% filter(x_mem != 0) %>% filter(y_mem != 0)
    lm(Mean ~ x_mem^2 + y_mem^2, filtered)
  }

  # Used for DivideInteger, QuotientInteger, RemainderInteger, ModInteger
  divideIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "DivideInteger") %>% filter(x_mem != 0) %>% filter(y_mem != 0)
    # This one does seem to underestimate the cost by a factor of two
    lm(Mean ~ ifelse(x_mem > y_mem, x_mem + y_mem, 0) , filtered)
  }

  # Used for LessThanInteger, GreaterThanInteger
  lessThanIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "LessThanInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }

  # Used for LessThanEqInteger, GreaterThanEqInteger
  lessThanEqIntegerModel <- {
    filtered <- data %>% filter(BuiltinName == "LessThanEqInteger") %>% filter(x_mem == y_mem) %>% filter (x_mem != 0)
    lm(Mean ~ I(pmin(x_mem, y_mem)), data=filtered)
  }

  list(
    addIntegerModel=addIntegerModel,
    eqIntegerModel=eqIntegerModel,
    subtractIntegerModel=subtractIntegerModel,
    multiplyIntegerModel=multiplyIntegerModel,
    divideIntegerModel=divideIntegerModel,
    lessThanIntegerModel=lessThanIntegerModel,
    lessThanEqIntegerModel=lessThanEqIntegerModel)
}