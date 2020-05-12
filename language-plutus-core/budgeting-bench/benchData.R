local({r <- getOption("repos")
       r["CRAN"] <- "http://cran.r-project.org" 
       options(repos=r)
})

# TODO nix should take care of this
# install.packages("tidyverse")
library(ggplot2)
library(dplyr)
library(stringr)
library(MASS)
library(broom)

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
  cbind(dat, mutated)
}