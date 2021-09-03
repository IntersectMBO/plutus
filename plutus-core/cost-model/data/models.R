## Suppress some annoying warnings
library(dplyr,   quietly=TRUE, warn.conflicts=FALSE)
library(stringr, quietly=TRUE, warn.conflicts=FALSE)
library(MASS,    quietly=TRUE, warn.conflicts=FALSE)
library(broom,   quietly=TRUE, warn.conflicts=FALSE)

## This causes warnings generated here to be printed out when this code is run from Haskell.
options (warn=1)

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
## was generated. Currently the inputs for all of our builtins are quite
## uniformly distributed, but if we ever have a case where there's a big
## variation of scales in the results (for instance if sizes grow exponentially)
## then there would be a danger of throwing away sensible results.  When we have
## a narrow range of input sizes (eg, for integer buitlins where sizes "only" go
## up to 31 words) outliers do occur and could cause problems. A warning will be
## issued by discard.upper.outliers if more than 10% of the datapoints are
## discarded, which whould reduce the danger of using the function on
## inappropriate data.
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
        stringsAsFactors=FALSE
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

filter.and.check.nonempty <- function (frame, name) {
    filtered <- filter (frame, BuiltinName == name)
##    cat (sprintf ("Reading data for %s\n", name))
    if (nrow(filtered) == 0) {
        stop ("No data found for ", name)
    } else filtered

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

    nops <- c("Nop1", "Nop2", "Nop3", "Nop4", "Nop5", "Nop6")
    overhead <- sapply(nops, get.mean.time)

    discard.overhead <- function(frame, name) {
        args.overhead <- overhead[arity(name)]
        mean.time <- mean(frame$Mean)
        if (mean.time > args.overhead) {
            mutate(frame,across(c("Mean", "MeanLB", "MeanUB"), function(x) { x - args.overhead }))
        }
        else {
            warning ("* NOTE: mean time for ",
                     name,
                     " was less than overhead (",
                     sprintf ("%.3f ms", mean.time),
                     " < ",
                     sprintf ("%.3f ms", args.overhead),
                     "): data was not adjusted");
            frame  ## ... or set the time to zero?
        }
    }

    constantModel <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty (fname) %>%
            discard.upper.outliers (fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ 1, data=filtered)
        adjustModel (m,fname)
    }

    ## filtered leaks from one model to the next, so make sure you don't mistype!

    ##### Integers #####

    addIntegerModel <- {
        fname <- "AddInteger"
        filtered <- data %>%
            filter.and.check.nonempty (fname)  %>%
            discard.upper.outliers (fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ pmax(x_mem, y_mem), filtered)
        adjustModel (m, fname)
    }

    subtractIntegerModel <- addIntegerModel

    multiplyIntegerModel <- {
        fname <- "MultiplyInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname)  %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ I(x_mem + y_mem), filtered)
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
            discard.upper.outliers(fname)   %>%
            discard.overhead (fname)
        m <- lm(Mean ~ I(x_mem * y_mem), filtered)
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
            discard.upper.outliers("EqualsInteger") %>%
            discard.overhead (fname)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanIntegerModel <- {
        fname <- "LessThanInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanEqualsIntegerModel <- {
        fname <- "LessThanEqualsInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }


    ##### Bytestrings #####

    appendByteStringModel <- {
        fname <- "AppendByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ I(x_mem + y_mem), data=filtered)
        adjustModel(m,fname)
    }
    ## Note that this is symmetrical in the arguments: a new bytestring is
    ## created and the contents of both arguments are copied into it.

    consByteStringModel  <- {
        fname <- "ConsByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ y_mem, data=filtered)
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
            discard.upper.outliers (fname) %>%
            filter(x_mem == y_mem) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    lessThanByteStringModel <- {
        fname <- "LessThanByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ pmin(x_mem, y_mem), data=filtered)
        adjustModel(m,fname)
    }

    lessThanEqualsByteStringModel <- lessThanByteStringModel  ## Check this!

    ## Cryptography and hashes

    sha2_256Model <- {
        fname <- "Sha2_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    sha3_256Model <- {
        fname <- "Sha3_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
      m <- lm(Mean ~ x_mem, data=filtered)
      adjustModel(m,fname)
    }

    blake2bModel <- {
        fname <- "Blake2b_256"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
      m <- lm(Mean ~ x_mem, data=filtered)
      adjustModel(m,fname)
    }

    ## This appears to be kind of random, even up to size 120000
    verifySignatureModel <- {
        fname <- "VerifySignature"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }


    ##### Strings #####

    appendStringModel <- {
        fname <- "AppendString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter (x_mem > 0 & y_mem > 0)    %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ I(x_mem + y_mem), data=filtered)  ## Both strings are copied in full
        adjustModel(m,fname)
    }

    equalsStringModel <- {
        fname <- "EqualsString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    decodeUtf8Model <- {
        fname <- "DecodeUtf8"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
        adjustModel(m,fname)
    }

    encodeUtf8Model <- {
        fname <- "DecodeUtf8"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.upper.outliers(fname) %>%
            discard.overhead (fname)
        m <- lm(Mean ~ x_mem, data=filtered)
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
    ## large bytestring, and the comaprison times for these are likely to be
    ## different.  Experiments with randomly generated heterogeneous data shows
    ## that if you plot time taken against memory usage then you get a fan
    ## shape, with all of the data lying below a particular straight line.  We
    ## want to identify that line here and return it as an upper bound for
    ## execution time.

    equalsDataModel   <- 0   ## MISSING

    mkPairDataModel     <- constantModel ("MkPairData")
    mkNilDataModel      <- constantModel ("MkNilData")
    mkNilPairDataModel  <- constantModel ("MkNilPairData")

    warnings() ## 

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
        mkNilPairDataModel            = mkNilPairDataModel
    )
}
