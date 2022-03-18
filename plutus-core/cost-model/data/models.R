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
## 10^(-6) seconds. WE SCALE THESE UP TO MILLISECONDS because the resulting
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
## relatively uniformly distributed., and this depends on how the benchmarking
## data was generated.  A warning will be issued by discard.upper.outliers if
## more than 10% of the datapoints are discarded, which whould reduce the danger
## of using the function on inappropriate data.
#
upper.outlier.cutoff <- function(v) {
    q1 <- quantile(v,0.25)
    q3 <- quantile(v,0.75)
    q3 + 1.5*(q3-q1)
}

discard.upper.outliers <- function(fr,fname) {
    cutoff <- upper.outlier.cutoff(fr$t.mean.ub)
    new.fr <- filter(fr, t.mean.ub < cutoff)
    nrows = nrow(fr)
    new.nrows = nrow(new.fr)
    if (new.nrows <= 0.9 * nrows) {
        cat (sprintf ("*** WARNING: %d outliers have been discarded from %d datapoints for %s\n", nrows-new.nrows, nrows, fname ));
    }
    return (new.fr)
}

arity <- function(name) {
    switch (name,
        "AddInteger" = 2,
        "SubtractInteger" = 2,
        "MultiplyInteger" = 2,
        "DivideInteger" = 2,
        "QuotientInteger" = 2,
        "RemainderInteger" = 2,
        "ModInteger" = 2,
        "EqualsInteger" = 2,
        "LessThanInteger" = 2,
        "LessThanEqualsInteger" = 2,
        "AppendByteString" = 2,
        "ConsByteString" = 2,
        "SliceByteString" = 3,
        "LengthOfByteString" = 1,
        "IndexByteString" = 2,
        "EqualsByteString" = 2,
        "LessThanByteString" = 2,
        "LessThanEqualsByteString" = 2,
        "Sha2_256" = 1,
        "Sha3_256" = 1,
        "Blake2b_256" = 1,
        "VerifySignature" = 3,
        "AppendString" = 2,
        "EqualsString" = 2,
        "EncodeUtf8" = 1,
        "SerialiseData" = 1,
        "DecodeUtf8" = 1,
        "IfThenElse" = 3,
        "ChooseUnit" = 2,
        "Trace" = 2,
        "FstPair" = 1,
        "SndPair" = 1,
        "ChooseList" = 3,
        "MkCons" = 2,
        "HeadList" = 1,
        "TailList" = 1,
        "NullList" = 1,
        "ChooseData" = 6,
        "ConstrData" = 2,
        "MapData" = 1,
        "ListData" = 1,
        "IData" = 1,
        "BData" = 1,
        "UnConstrData" = 1,
        "UnMapData" = 1,
        "UnListData" = 1,
        "UnIData" = 1,
        "UnBData" = 1,
        "EqualsData" = 2,
        "MkPairData" = 2,
        "MkNilData" = 1,
        "MkNilPairData" = 1
        )
}


## Read a file containing Criterion CSV output and convert it to a frame
get.bench.data <- function(path) {
    dat <- read.csv(
        path,
        header=TRUE,
        stringsAsFactors=FALSE,
        comment.char="#"
    )

    benchname <- regex("([[:alnum:]_]+)/ExMemory (\\d+)(?:/ExMemory (\\d+))?(?:/ExMemory (\\d+))?")
    ## We have benchmark names like "AddInteger/ExMemory 11/ExMemory 22".  This extracts the name
    ## and up to three numbers, returning "NA" for any that are missing.  If we ever have builtins
    ## with more than three arguments we'lll need to extend this and add names for the new arguments.

    ## FIXME: the benchmarks for Nop4, Nop5, and Nop6 do have more than three
    ## arguments, but we're not paying any attention to the extra ones because
    ## the cost is constant.  ChooseData takes six arguments, but we only record
    ## the size of the first one because the others are terms (and the time is
    ## constant anyway).

    numbercols = c("x_mem", "y_mem", "z_mem")

    benchmark_name_to_numbers <- function(name) {
        a <- str_match(name, benchname)
        r <- as.data.frame(a[,-1]) # Discard the first column (which is the entire match)
        names(r) <- c("name", numbercols)
        return (r)
    }

    numbers <- benchmark_name_to_numbers(dat$benchmark)

    mutated <- numbers %>%
                  mutate(across(all_of(numbercols), function(x) { as.numeric(as.character(x))})) %>%
                  mutate(across("name", as.character))

    cbind(dat, mutated) %>%
        mutate(across(c("t", "t.mean.lb", "t.mean.ub", "t.sd", "t.sd.lb", "t.sd.ub"), seconds.to.milliseconds))
}

filter.and.check.nonempty <- function (frame, fname) {
    filtered <- filter (frame, name == fname)
##    cat (sprintf ("Reading data for %s\n", name))
    if (nrow(filtered) == 0) {
        stop ("No data found for ", fname)
    } else filtered

}


adjustModel <- function (m, fname) {
    ## Given a linear model, check its coefficients and if any is negative then
    ## make it 1000 and issue a warning.  This is somewhat suspect but will
    ## prevent us from getting models which predict negative costs.
    ## See also https://stackoverflow.com/questions/27244898/force-certain-parameters-to-have-positive-coefficients-in-lm

    default <- 1/1000  ## 1 ns, or 1000 ps (remember we're working in ms here)
    ensurePositive <- function(x, name) {
        if (x<0) {
            cat (sprintf("** WARNING: a negative coefficient %f for %s occurred in the model for %s. This has been adjusted to %s.\n",
                         x, name, fname, default))
            default
        }
        else x
    }
    v <- m$coefficients
    m$coefficients <- mapply(ensurePositive, v, attr(v,"names"))
    ## This will invalidate some of the information in the model (such as the
    ## residuals), but we don't use that anyway.  Maybe we should just return the
    ## vector of coefficients?
    return (m)
}


modelFun <- function(path) {
##    cat ("** Reading CSV, creating R models **\n")
    data <- get.bench.data(path)

    ## Look for a single entry with the given name and return the 't' value
    ## (ie, the mean execution time) for that entry.  If <name> occurs multiple
    ## times, return the mean value, and if it's not present return zero,
    ## issuing a warning in both cases
    get.mean.time <- function(fname) {
        t <- data %>% filter (name == fname)  %>% dplyr::pull("t")  # NOT 'select': we need a vector here, not a frame.
        len <- length(t)

        if (len == 1) {
            r <- t
        }
        else if (len == 0) {
            cat(sprintf ("* WARNING: %s not found in input - returning 0\n", fname))
            r <- 0
        } else {
            cat(sprintf ("* WARNING: multiple entries for %s in input - returning mean value\n", fname))
            r <- mean(t)
        }

        if (r < 0) {
            cat (sprintf ("* WARNING: mean time for %s is negative - returning 0\n", fname))
            return (0)
        }
        return (r)
    }


    ## We have benchmarks which measure the cost of calling no-op benchmarks
    ## which unlift their arguments in a number of different ways.  The ones we
    ## use here are for nops taking Opaque arguments.  Heuristically this
    ## appears to give a good trade-off between including the overhead in the
    ## cost of calling the benchmark and absorbing it in the cost of a CEK
    ## machine step.
    nops <- c("Nop1o", "Nop2o", "Nop3o", "Nop4o", "Nop5o", "Nop6o")
    overhead <- sapply(nops, get.mean.time)


    ## The next function discards the overhead for calling a builtin, as
    ## determined by the Nop* benchmarks.  This means that the costing function
    ## should just measure the cost of running the denotation; we assume that
    ## the overhead of applyEvalute and so on in the evaluator is absorbed in the
    ## average cost of a CEK step.  
    discard.overhead <- function(frame, fname) {
        args.overhead <- overhead[arity(fname)]
        mean.time <- mean(frame$t)
        if (mean.time > args.overhead) {
            mutate(frame,across(c("t", "t.mean.lb", "t.mean.ub"), function(x) { x - args.overhead }))
        }
        else {
            ## Sometimes the total time taken to run a builtin is less than the
            ## cost of a Nop (don't know why), so the adjusted time would be
            ## negative.  In this case we set the time to a small default.
            
            default = 0.001  ## 0.001 microseconds, ie 1 nanosecond.
            ## For some reason, making the default 0 causes a failure when the model is read from R:
            ##   `Failed reading: conversion error: expected Double, got "NA" (Failed reading: takeWhile1)) at ""`

            cat (sprintf ("* NOTE: mean time for %s was less than overhead (%.3f ms < %.3f ms): adjusted time set to %.1f ns\n",
                          fname, mean.time, args.overhead, default*1000));
            mutate(frame,across(c("t", "t.mean.lb", "t.mean.ub"), function(x) { default }))
        }
    }

    constantModel <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty (fname) %>%
            discard.upper.outliers (fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ 1, data=filtered)
        adjustModel (m,fname)
    }

    ##### Integers #####

    addIntegerModel <- {
        fname <- "AddInteger"
        filtered <- data %>%
            filter.and.check.nonempty (fname)  %>%
            discard.overhead (fname)
        m <- lm(t ~ pmax(x_mem, y_mem), filtered)
        adjustModel (m, fname)
    }

    subtractIntegerModel <- addIntegerModel

    multiplyIntegerModel <- {
        fname <- "MultiplyInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname)  %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.overhead (fname)
        m <- lm(t ~ I(x_mem + y_mem), filtered)
        adjustModel (m, fname)
    }
    ## We do want I(x+y) here ^: the cost is linear, but symmetric.


    ## This is very compilcated.  It's constant above the diagonal but quadratic
    ## below it.  For now we fit a crude model to the below-diagonal part and
    ## an arbitrary value above the diagonal (see CreateCostModel.hs).  Later
    ## we should find the actual mean value above the diagonal and try to
    ## fit a better model below it.
    divideIntegerModel <- {
        fname <- "DivideInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname)    %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            filter (x_mem > y_mem) %>%
            discard.overhead (fname)
        m <- lm(t ~ I(x_mem * y_mem), filtered)
        adjustModel(m,fname)
    }

    quotientIntegerModel  <- divideIntegerModel
    remainderIntegerModel <- divideIntegerModel
    modIntegerModel       <- divideIntegerModel

    equalsIntegerModel <- {
        fname <- "EqualsInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead (fname)
        m <- lm(t ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanIntegerModel <- {
        fname <- "LessThanInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead (fname)
        m <- lm(t ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanEqualsIntegerModel <- {
        fname <- "LessThanEqualsInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead (fname)
        m <- lm(t ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }


    ##### Bytestrings #####

    appendByteStringModel <- {
        fname <- "AppendByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.overhead (fname)
        m <- lm(t ~ I(x_mem + y_mem), data=filtered)
        adjustModel(m,fname)
    }
    ## Note that this is symmetrical in the arguments: a new bytestring is
    ## created and the contents of both arguments are copied into it.

    consByteStringModel  <- {
        fname <- "ConsByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ y_mem, data=filtered)
        adjustModel(m,fname)
    }
    ## Depends on the size of the second argument, which has to be copied into
    ## the destination.

    sliceByteStringModel <- constantModel ("SliceByteString")
    ## Bytetrings are immutable arrays with a pointer to the start and a length.
    ## This just adjusts the pointer and length.

    lengthOfByteStringModel <- constantModel ("LengthOfByteString")  ## Just returns a field
    indexByteStringModel    <- constantModel ("IndexByteString")     ## Constant-time array access

    equalsByteStringModel <- {
        fname <- "EqualsByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    lessThanByteStringModel <- {
        fname <- "LessThanByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanEqualsByteStringModel <- lessThanByteStringModel  ## Check this!

    ## Cryptography and hashes

    sha2_256Model <- {
        fname <- "Sha2_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    sha3_256Model <- {
        fname <- "Sha3_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
      m <- lm(t ~ x_mem, data=filtered)
      adjustModel(m,fname)
    }

    blake2bModel <- {
        fname <- "Blake2b_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
      m <- lm(t ~ x_mem, data=filtered)
      adjustModel(m,fname)
    }

    ## verifySignature in fact takes three arguments, but the first and third
    ## are of fixed size, so we only gather benchmarking data for different
    ## sizes of the second argument (the "message" being signed).  This can be
    ## very large, but the time appears to be kind of random, even up to size
    ## 120000.  This is somewhat confusing because the CSV file only contains
    ## results for the x parameter but in fact it refers to the second parameter
    ## of verifySignature.  To clarify things here we should probably record data
    ## for all three parameter sizes even though the first and third are constant.
    verifySignatureModel <- {
        fname <- "VerifySignature"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }


    ##### Strings #####

    appendStringModel <- {
        fname <- "AppendString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter (x_mem > 0 & y_mem > 0)    %>%
            discard.overhead (fname)
        m <- lm(t ~ I(x_mem + y_mem), data=filtered)  ## Both strings are copied in full
        adjustModel(m,fname)
    }

    equalsStringModel <- {
        fname <- "EqualsString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    decodeUtf8Model <- {
        fname <- "DecodeUtf8"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    encodeUtf8Model <- {
        fname <- "EncodeUtf8"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }


    ##### Bool #####

    ifThenElseModel <- constantModel ("IfThenElse")


    ##### Unit #####

    chooseUnitModel <- constantModel ("ChooseUnit")


    ##### Tracing #####

    traceModel <- constantModel ("Trace")


    ##### Pairs #####

    fstPairModel <- constantModel ("FstPair")
    sndPairModel <- constantModel ("SndPair")


    ##### Lists #####

    chooseListModel <- constantModel ("ChooseList")
    mkConsModel     <- constantModel ("MkCons")
    headListModel   <- constantModel ("HeadList")
    tailListModel   <- constantModel ("TailList")
    nullListModel   <- constantModel ("NullList")


    ##### Data #####

    chooseDataModel   <- constantModel ("ChooseData")
    constrDataModel   <- constantModel ("ConstrData")
    mapDataModel      <- constantModel ("MapData" )
    listDataModel     <- constantModel ("ListData")
    iDataModel        <- constantModel ("IData")
    bDataModel        <- constantModel ("BData")
    unConstrDataModel <- constantModel ("UnConstrData")
    unMapDataModel    <- constantModel ("UnMapData")
    unListDataModel   <- constantModel ("UnListData")
    unIDataModel      <- constantModel ("UnIData")
    unBDataModel      <- constantModel ("UnBData")


    ## equalsData is tricky because it uses the Eq instance for Data, which
    ## can't call costing functions for embedded Integers and Text objects.  We
    ## only have one number to measure the memory usage of a Data object and it
    ## can't disinguish between an object with lots of nodes and not much atomic
    ## data and an object with a small number of nodes each containing e.g. a
    ## large bytestring, and the comparison times for these are likely to be
    ## different.

    ## Experiments with randomly generated heterogeneous data shows that if you
    ## plot time taken against memory usage then you get a fan shape, with all
    ## of the data lying below a particular straight line.  We want to identify
    ## that line here and return it as an upper bound for execution time.

    ## Heuristically, the following procedure appears to give good results.
    ## With the current distribution of input data, about 10% of our 400 data
    ## points for EqualsData have the smallest possible size (4, for a single
    ## node containing an empty list).  We calculate the mean time (min.t) for
    ## data points with this x-coordinate (min.x), then fit a linear model
    ## constrained to pass through this point and look at its slope, s.  Since
    ## this is a bit fragile, we print out some information about accuracy.

    ## In the longer term we should try to find a better size estimate for Data.
    ## This might allow us to get better predicitions, although it's likely that
    ## the "memoryUsage" value would not represent actual memory usage, but
    ## rather the cost of processing nodes in a Data tree vis-a-vis the cost
    ## of processing integers and bytestrings.
 
    equalsDataModel   <- {
        fname <- "EqualsData"
        f <- data %>% filter.and.check.nonempty(fname)
        min.x <- min(f$x_mem)
        min.t <- mean (f$t[f$x_mem==min.x])
        m <- lm(f$t - min.t ~ I(f$x_mem - min.x) + 0)
        s <- coef(m)[1]  ## Not 2: we've used +0, so the intercept doesn't appear in the model
        v <- c(min.t-s*min.x, s) ## ie, f(x) = min.t +s(x-min.x)
        pr <- function(x) { v[1] + v[2]*x }  ## What this model predicts.
        errors = (f$t-pr(f$x))/f$t  ## Residuals as fraction of observed values.
        over = -errors[errors<0]   ## Overpredictions (observed value < prediction) - good, or at least acceptable.
        under = errors[errors>=0]  ## Underpredictions (observed value >= prediction) - bad
        cat (sprintf("# INFO: EqualsData: prediction is an underestimate for %.1f%% of observations.  Maximum underestimate = %.1f%%, mean = %.1f%%\n",
            (length(under)/length(errors))*100,  max(under)*100, mean(under)*100))
        cat (sprintf("# INFO: EqualsData: prediction is an overestimate for %.1f%% of observations.  Maximum overestimate = %.1f%%, mean = %.1f%%\n",
            (length(over)/length(errors))*100,  max(over)*100, mean(over)*100))
        names(v) <- c("(Intercept)", "pmin(x_mem, y_mem)")  ## Make it look like what the Haskell code's expecting. The space after the comma is important.
        m2 <- lm(t ~ pmin(x_mem, y_mem), data=f) ## A model with the structure expected by CostModelCreation.
        m2$coefficients <- v   ## The rest of the data in the model now becomes nonsensical, but we don't use it.
        adjustModel(m2,fname)
    }

    serialiseDataModel <- {  # FIXME
        fname <- "SerialiseData"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(t ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }


    mkPairDataModel     <- constantModel ("MkPairData")
    mkNilDataModel      <- constantModel ("MkNilData")
    mkNilPairDataModel  <- constantModel ("MkNilPairData")

    list(
        addIntegerModel               = addIntegerModel,
        subtractIntegerModel          = subtractIntegerModel,
        multiplyIntegerModel          = multiplyIntegerModel,
        divideIntegerModel            = divideIntegerModel,
        quotientIntegerModel          = quotientIntegerModel,
        remainderIntegerModel         = remainderIntegerModel,
        modIntegerModel               = modIntegerModel,
        equalsIntegerModel            = equalsIntegerModel,
        lessThanIntegerModel          = lessThanIntegerModel,
        lessThanEqualsIntegerModel    = lessThanEqualsIntegerModel,
        appendByteStringModel         = appendByteStringModel,
        consByteStringModel           = consByteStringModel,
        sliceByteStringModel          = sliceByteStringModel,
        lengthOfByteStringModel       = lengthOfByteStringModel,
        indexByteStringModel          = indexByteStringModel,
        equalsByteStringModel         = equalsByteStringModel,
        lessThanByteStringModel       = lessThanByteStringModel,
        lessThanEqualsByteStringModel = lessThanEqualsByteStringModel,
        sha2_256Model                 = sha2_256Model,
        sha3_256Model                 = sha3_256Model,
        blake2bModel                  = blake2bModel,
        verifySignatureModel          = verifySignatureModel,
        appendStringModel             = appendStringModel,
        equalsStringModel             = equalsStringModel,
        encodeUtf8Model               = encodeUtf8Model,
        decodeUtf8Model               = decodeUtf8Model,
        ifThenElseModel               = ifThenElseModel,
        chooseUnitModel               = chooseUnitModel,
        traceModel                    = traceModel,
        fstPairModel                  = fstPairModel,
        sndPairModel                  = sndPairModel,
        chooseListModel               = chooseListModel,
        mkConsModel                   = mkConsModel,
        headListModel                 = headListModel,
        tailListModel                 = tailListModel,
        nullListModel                 = nullListModel,
        chooseDataModel               = chooseDataModel,
        constrDataModel               = constrDataModel,
        mapDataModel                  = mapDataModel,
        listDataModel                 = listDataModel,
        iDataModel                    = iDataModel,
        bDataModel                    = bDataModel,
        unConstrDataModel             = unConstrDataModel,
        unMapDataModel                = unMapDataModel,
        unListDataModel               = unListDataModel,
        unIDataModel                  = unIDataModel,
        unBDataModel                  = unBDataModel,
        equalsDataModel               = equalsDataModel,
        mkPairDataModel               = mkPairDataModel,
        mkNilDataModel                = mkNilDataModel,
        mkNilPairDataModel            = mkNilPairDataModel,
        serialiseDataModel            = serialiseDataModel
    )
}
