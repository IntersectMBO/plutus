## Suppress some annoying warnings
library(dplyr,   quietly=TRUE, warn.conflicts=FALSE)
library(stringr, quietly=TRUE, warn.conflicts=FALSE)
library(MASS,    quietly=TRUE, warn.conflicts=FALSE)
library(broom,   quietly=TRUE, warn.conflicts=FALSE)

## See Note [Creation of the Cost Model]

## This R code is used to analyse the data in `benching.csv` produced by
## plutus-core:cost-model-budgeting-bench using the code in plutus-core/budgeting-bench/Bench.hs.
## It's tailored to fit the shape of that data, so alterations to Bench.hs may
## require changes here to get sensible results.


## At present, times in the becnhmarking data are typically of the order of
## 10^(-6) seconds. We scale these up to milliseconds because the resulting
## numbers are much easier to work with interactively.  For use in the Plutus
## Core cost model we scale times up by a further factor of 10^6 (to
## picoseconds) because then everything fits into integral values with little
## loss of precision.  This is safe because we're only using models which
## are linear in their inputs.

seconds.to.milliseconds <- function(x) { x * 1e6 }

## Discard any datapoints whose execution time is greater than 1.5 times the
## interquartile range above the third quartile, as is done in boxplots.  In our
## benchmark results we occasionally get atypically large times which throw the
## models off and discarding the outliers helps to get a reasonable model
#
## This should only be used on data which can reasonably be assumed to be
## relatively evenly distributed, and this depends on how the benchmarking data
## was generated. Currently the inputs for integer builtins are OK, but the
## inputs for bytestring builtins grow exponentially, so there's a big variation
## of scales in the results and there's a danger of throwing away sensible
## results.  The bytestring buitlins seem to behave pretty regularly, so we
## still get good models.  However, we're looking at a much narrower range of
## input sizes for integers ("only" up to 31 words) and there outliers do cause
## problems.  A warning will be issued by discard.upper.outliers if more than
## 10% of the datapoints are discarded, which whould reduce the danger of using
## the function on inappropriate data.
#
upper.outlier.cutoff <- function(v) {
    q1 <- quantile(v,0.25)
    q3 <- quantile(v,0.75)
    q3 + 1.5*(q3-q1)
}

discard.upper.outliers <- function(fr,name) {
    cutoff <- upper.outlier.cutoff(fr$MeanUB)
    new.fr <- filter(fr, MeanUB < cutoff)
    nrows = nrow(fr)
    new.nrows = nrow(new.fr)
    if (new.nrows <= 0.9 * nrows) {
        warning ("*** WARNING: ", nrows-new.nrows, " outliers have been discarded from ", nrows, " datapoints for ", name );
    }
    new.fr
}


## Read a file containing Criterion CSV output and convert it to a frame
get.bench.data <- function(path) {
    dat <- read.csv(
        path,
        header=TRUE,
        stringsAsFactors=FALSE
    )

    benchname <- regex("([:alnum:]+)/ExMemory (\\d+)(?:/ExMemory (\\d+))?(?:/ExMemory (\\d+))?")
    ## We have benchmark names like "AddInteger/ExMemory 11/ExMemory 22".  This extracts the name
    ## and up to three numbers, returning "NA" for any that are missing.  If we ever have builtins
    ## with more than three arguments we'lll need to extend this and add names for the new arguments.

    numbercols = c("x_mem", "y_mem", "z_mem")

    benchmark_name_to_numbers <- function(name) {
        a <- str_match(name, benchname)
        r <- as.data.frame(a[,-1]) # Discard the first column (which is the entire match)
        names(r) <- c("BuiltinName", numbercols)
        r
    }

    numbers <- benchmark_name_to_numbers(dat$Name)

    mutated <- numbers %>%
                  mutate(across(all_of(numbercols), function(x) { as.numeric(as.character(x))})) %>%
                  mutate(across("BuiltinName", as.character))

    cbind(dat, mutated) %>%
        mutate(across(c("Mean", "MeanLB", "MeanUB", "Stddev", "StddevLB", "StddevUB"), seconds.to.milliseconds))
}

discard.overhead <- function(frame, overhead) {
    mutate(frame,across(c("Mean", "MeanLB", "MeanUB"), function(x) { x-overhead }))
}

adjustModel <- function (m, fname) {
    ## Given a linear model, check its coefficients and if any is negative then
    ## make it zero and issue a warning.  This is somewhat suspect but will prevent
    ## us from getting models which predict negative costs.

    ## See also https://stackoverflow.com/questions/27244898/force-certain-parameters-to-have-positive-coefficients-in-lm

    ensurePositive <- function(x, name) {
        if (x<0) {
            warning ("*** WARNING: a negative coefficient ", x, " for ", name,
                     "\n  *** occurred in the model for ", fname, ". This has been adjusted to zero.");
            0
        }
        else x
    }
    v <- m$coefficients
    m$coefficients <- mapply(ensurePositive, v, attr(v,"names"))
    ## This will invalidate some of the information in the model (such as the
    ## residuals), but we don't use that anyway.  Maybe we should just return the
    ## vector of coefficients?
    m
}

modelFun <- function(path) {
    data <- get.bench.data(path)

    ## Look for a single entry with the given name and return the "Mean" value
    ## (ie, the mean execution time) for that entry.  If <name> occurs multiple
    ## times, return the mean value, and if it's not present return zero,
    ## issuing a warning in both cases
    get.mean.time <- function(name) {
        t <- data %>% filter (BuiltinName == name)  %>% dplyr::pull("Mean")  # NOT 'select': we need a vector here, not a frame.
        len <- length(t)

        if (len == 1) {
            r <- t
        }
        else if (len == 0) {
            warning (sprintf ("*** WARNING: %s not found in input - returning 0", name))
            r <- 0
        } else {
            warning (sprintf ("*** WARNING: multiple entries for %s in input - returning mean value", name))
            r <- mean(t)
        }

        if (r < 0) {
            warning (sprintf ("*** WARNING: mean time for %s is negative - returning 0", name))
            return (0)
        }
        return (r)
    }

    one.arg.overhead    <- get.mean.time("Nop1")
    two.args.overhead   <- get.mean.time("Nop2")
    three.args.overhead <- get.mean.time("Nop3")

    ## filtered leaks from one model to the next, so make sure you don't mistype!

    addIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "AddInteger")  %>%
            discard.upper.outliers("AddInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmax(x_mem, y_mem), filtered)
        adjustModel (m, "AddInteger")
    }

    subtractIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "SubtractInteger")  %>%
            discard.upper.outliers("SubtractInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmax(x_mem , y_mem), filtered)
        adjustModel (m, "SubtractInteger")
    }

    multiplyIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "MultiplyInteger")  %>%
            filter(x_mem != 0) %>% filter(y_mem != 0) %>%
            discard.upper.outliers("MultiplyInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ I(x_mem + y_mem), filtered)
        adjustModel (m, "MultiplyInteger")
    }
    ## We do want I(x+y) here ^: the cost is linear, but symmetric.

    divideIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "DivideInteger")    %>%
            filter(x_mem != 0) %>% filter(y_mem != 0) %>%
            discard.upper.outliers("DivideInteger")   %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ ifelse(x_mem > y_mem, I(x_mem * y_mem), 0) , filtered)
        adjustModel(m,"DivideInteger")
    }
    ## This one does seem to underestimate the cost by a factor of two.
    ## TODO: fix this.  It's hard to see what's going on, but an estimate of
    ## twice the cost of multiplication looks safe. Get some more data to check that.

    quotientIntegerModel  <- divideIntegerModel
    remainderIntegerModel <- divideIntegerModel
    modIntegerModel       <- divideIntegerModel

    eqIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "EqInteger") %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem != 0) %>%
            discard.upper.outliers("EqInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,"EqInteger")
    }

    lessThanIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "LessThanInteger") %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem != 0) %>%
            discard.upper.outliers("LessThanInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,"LessThanInteger")
    }

    greaterThanIntegerModel <- lessThanIntegerModel

    lessThanEqIntegerModel <- {
        filtered <- data %>%
            filter(BuiltinName == "LessThanEqInteger") %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem != 0) %>%
            discard.upper.outliers("LessThanEqInteger") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,"LessThanEqInteger")
    }

    greaterThanEqIntegerModel <- lessThanEqIntegerModel

    eqByteStringModel <- {  # We're not discarding outliers because the input sizes in Bench.hs grow exponentially.
        filtered <- data %>%
            filter(BuiltinName == "EqByteString") %>%
            filter(x_mem == y_mem) %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,"EqByteString")
    }

    ltByteStringModel <- {
        filtered <- data %>%
            filter(BuiltinName == "LtByteString") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,"LtByteString")
    }

    gtByteStringModel <- ltByteStringModel

    concatenateModel <- {
        filtered <- data %>%
            filter(BuiltinName == "Concatenate") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ I(x_mem + y_mem), data=filtered)
        adjustModel(m,"Concatenate")
    }
    ## TODO: is this symmetrical in the arguments?  The data suggests so, but check the implementation.

    takeByteStringModel <- {
        filtered <- data %>%
            filter(BuiltinName == "TakeByteString") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ 1, data=filtered)
        adjustModel(m,"TakeByteString")
    }

    dropByteStringModel <- {
        filtered <- data %>%
            filter(BuiltinName == "DropByteString") %>%
            discard.overhead (two.args.overhead)
        m <- lm(Mean ~ 1, data=filtered)
        adjustModel(m,"DropByteString")
    }

    sHA2Model <- {
        filtered <- data %>%
            filter(BuiltinName == "SHA2") %>%
            discard.overhead (one.arg.overhead)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,"SHA2")
    }

    sHA3Model <- {
        filtered <- data %>%
            filter(BuiltinName == "SHA3") %>%
            discard.overhead (one.arg.overhead)
      m <- lm(Mean ~ x_mem, data=filtered)
      adjustModel(m,"SHA3")
    }

    verifySignatureModel <- {
        filtered <- data %>%
            filter(BuiltinName == "VerifySignature") %>%
            discard.overhead (three.args.overhead)
        m <- lm(Mean ~ 1, data=filtered)
        adjustModel(m,"VerifySignature")
    }

    ifThenElseModel <- 0

    list(
        addIntegerModel            = addIntegerModel,
        eqIntegerModel             = eqIntegerModel,
        subtractIntegerModel       = subtractIntegerModel,
        multiplyIntegerModel       = multiplyIntegerModel,
        divideIntegerModel         = divideIntegerModel,
        quotientIntegerModel       = quotientIntegerModel,
        remainderIntegerModel      = remainderIntegerModel,
        modIntegerModel            = modIntegerModel,
        lessThanIntegerModel       = lessThanIntegerModel,
        greaterThanIntegerModel    = greaterThanIntegerModel,
        lessThanEqIntegerModel     = lessThanEqIntegerModel,
        greaterThanEqIntegerModel  = greaterThanEqIntegerModel,
        concatenateModel           = concatenateModel,
        takeByteStringModel        = takeByteStringModel,
        dropByteStringModel        = dropByteStringModel,
        sHA2Model                  = sHA2Model,
        sHA3Model                  = sHA3Model,
        eqByteStringModel          = eqByteStringModel,
        ltByteStringModel          = ltByteStringModel,
        gtByteStringModel          = gtByteStringModel,
        verifySignatureModel       = verifySignatureModel,
        ifThenElseModel            = ifThenElseModel
    )

}
