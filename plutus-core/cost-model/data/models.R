## Suppress some annoying warnings
library(MASS,    quietly=TRUE, warn.conflicts=FALSE)
library(stringr, quietly=TRUE, warn.conflicts=FALSE)
library(dplyr,   quietly=TRUE, warn.conflicts=FALSE)
library(broom,   quietly=TRUE, warn.conflicts=FALSE)

## Let's see any warnings immediately instead of them being saved up to surprise
## us later on.
options(warn=1)

## See Note [Creation of the Cost Model]

## This R code is used to analyse the data in `benching.csv` produced by
## plutus-core:cost-model-budgeting-bench using the code in plutus-core/budgeting-bench/Bench.hs.
## It's tailored to fit the shape of that data, so alterations to Bench.hs may
## require changes here to get sensible results.


## At present, times in the benchmarking data are typically of the order of
## 10^(-6) seconds. WE SCALE THESE UP TO MICROSECONDS because the resulting
## numbers are much easier to work with interactively.  For use in the Plutus
## Core cost model we scale times up by a further factor of 10^6 (to
## picoseconds) because then everything fits into integral values with little
## loss of precision.  This is safe because we're only using models which
## are linear in their inputs.

seconds.to.microseconds <- function(x) { x * 1e6 }

## Discard any datapoints whose execution time is greater than 1.5 times the
## interquartile range above the third quartile, as is done in boxplots.  In our
## benchmark results we occasionally get atypically large times which throw the
## models off and discarding the outliers helps to get a reasonable model.
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

discard.upper.outliers <- function(fr) {
    fname <- fr$name[1]
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
    ## cat (sprintf ("Arity:  %s\n", name))  # Useful to see how far we get
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
        "VerifyEd25519Signature" = 3,
        "VerifyEcdsaSecp256k1Signature" = 3,
        "VerifySchnorrSecp256k1Signature" = 3,
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
        "MkNilPairData" = 1,
        "Bls12_381_G1_add" = 2 ,
        "Bls12_381_G1_neg" = 1,
        "Bls12_381_G1_scalarMul" = 2,
        "Bls12_381_G1_multiScalarMul" = 2,
        "Bls12_381_G1_equal" = 2,
        "Bls12_381_G1_hashToGroup" = 2,
        "Bls12_381_G1_compress" = 1,
        "Bls12_381_G1_uncompress" = 1,
        "Bls12_381_G2_add" = 2,
        "Bls12_381_G2_neg" = 1,
        "Bls12_381_G2_scalarMul" = 2,
        "Bls12_381_G2_multiScalarMul" = 2,
        "Bls12_381_G2_equal" = 2,
        "Bls12_381_G2_hashToGroup" = 2,
        "Bls12_381_G2_compress" = 1,
        "Bls12_381_G2_uncompress" = 1,
        "Bls12_381_millerLoop" = 2,
        "Bls12_381_mulMlResult" = 2,
        "Bls12_381_finalVerify" = 2,
        "Keccak_256" = 1,
        "Blake2b_224" = 1,
        "Ripemd_160" = 1,
        "IntegerToByteString" = 3,
        "ByteStringToInteger" = 2,
        "AndByteString" = 3,
        "OrByteString" = 3,
        "XorByteString" = 3,
        "ComplementByteString" = 1,
        "ReadBit" = 2,
        "WriteBits" = 2,
        "ReplicateByte" = 2,
        "ShiftByteString" = 2,
        "RotateByteString" = 2,
        "CountSetBits" = 1,
        "FindFirstSetBit" = 1,
        "ExpModInteger" = 3,
        "DropList" = 2,
        "LengthOfArray" = 1,
        "ListToArray" = 1,
        "IndexArray" = 2,
        "LookupCoin" = 3,
        "ValueContains" = 2,
        "ValueData" = 1,
        "UnValueData" = 1,
        -1  ## Default for missing values
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

    benchname <- regex("([[:alnum:]_]+)/(\\d+)(?:/(\\d+))?(?:/(\\d+))?")
    ## We have benchmark names like "AddInteger/11/22", the numbers representing the sizes of
    ## the inputs to the benchmark.  This extracts the name and up to three numbers, returning
    ## "NA" for any that are missing.  If we ever have builtins with more than three arguments
    ## we'll need to extend this and add names for the new arguments.

    ## FIXME: the benchmarks for Nop4, Nop5, and Nop6 do have more than three
    ## arguments, but we're not paying any attention to the extra ones because
    ## the cost is constant.  ChooseData takes six arguments, but we only record
    ## the size of the first one because the others are terms (and the time is
    ## constant anyway).

    numbercols = c("x_mem", "y_mem", "z_mem")

    benchmark.name.to.numbers <- function(name) {
        a <- str_match(name, benchname)
        r <- as.data.frame(a[,-1]) # Discard the first column (which is the entire match)
        names(r) <- c("name", numbercols)
        return (r)
    }

    numbers <- benchmark.name.to.numbers (dat$benchmark)

    mutated <- numbers %>%
        dplyr::mutate(across(all_of(numbercols), function(x) { as.numeric(as.character(x))})) %>%
        dplyr::mutate(across("name", as.character))

    cbind(dat, mutated) %>%
        mutate(across(c("t", "t.mean.lb", "t.mean.ub", "t.sd", "t.sd.lb", "t.sd.ub"), seconds.to.microseconds))
}

filter.and.check.nonempty <- function (frame, fname) {
    ## cat (sprintf ("Reading data for %s\n", fname))
    filtered <- filter (frame, name == fname)
    if (nrow(filtered) == 0) {
        stop ("No data found for ", fname)
    } else filtered

}

adjustModel <- function (r, fname) {
    ## Given a linear model, check its coefficients and if any is negative then
    ## make it 1000 ps and issue a warning.  This is somewhat suspect but will
    ## prevent us from getting models which predict negative costs.  See also
    ## https://stackoverflow.com/questions/27244898/force-certain-parameters-to-have-positive-coefficients-in-lm

    default <- 1/1000  ## 1 ns, or 1000 ps (remember: we're working in µs here)
    ensurePositive <- function(x, name) {
        if (x<0) {
            cat (sprintf("** WARNING: a negative coefficient %f for %s occurred in the model for %s. This has been adjusted to %s.\n",
                         x, name, fname, default))
            default
        }
        else x
    }
    v <- r$model$coefficients
    r$model$coefficients <- mapply(ensurePositive, v, attr(v,"names"))
    ## This will invalidate some of the information in the model (such as the
    ## residuals), but we don't use that anyway.  Maybe we should just return the
    ## vector of coefficients?

    if (exists("constant",where=r)) {
       if (r$constant < 0) r$constant=0.2 ## 0.2 ms = 200000 ps
    }
    return (r)
}

adjustModels <- function(models) {
    ## Given a list of named models, apply `adjustModel` to each entry to
    ## ensure that all of the model coefficients are positive.  This is applied
    ## to the entire list of models before returning them to the outside world.
    adjustEntry <- function(name) {
        adjustModel(models[[name]], sub("Model", "", name))
    }
    models2 <- lapply(names(models), adjustEntry)
    names(models2) <- names(models)
    # Can we just mutate the entries of `models` in place, leaving the names untouched?

    return(models2)
}


## Benchmark results for some functions involving Data exhibit a fan shape where
## all the data points lie above the x-axis but below some sloping straight line
## (this is because Data is heterogeneous but we only have a single size
## measure, and objects of the same size can have significantly different
## structures).  The "fit.fan" function is supposed to find an approximation
## t=ax+b to this line, which should provide a conservative upper bound for
## execution time in terms of input size. We do this by fitting a linear model,
## discarding all of the points below the regression line, and repeating until
## the number of underestimates produced by running the model on the full
## dataset is greater than some threshold (default 90%) or until a limit on the
## number of iterations (default 20) is exceeded.  If the process is iterated
## too many times you can end up getting errors because you've discarded all of
## the data.  Setting the do.plot argument to TRUE produces an informative plot,
## but this should only be used interactively.

fit.fan <- function(f, threshold=0.9, limit=20, do.plot=FALSE) {
    fname <- f$name[1]

    ## The benchmark data we currently have is concentrated towards the origin,
    ## which can cause some difficulty because lower values become too
    ## influential.  We force the model to have an intercept which causes most
    ## of the small-x data to lie below the regression line, although this
    ## complicates matters somewhat.

    min.x <- min(f$x_mem)           # Smallest x value
    min.ts <- f$t[f$x_mem==min.x]   # All of the t values for the smallest x value
    t0 <- quantile(min.ts,0.8)      # Fixed intercept

    npoints <- length(f$x_mem)
    g <- f   # f is the original data, g is a copy that's updated every time round the loop

    loops = 0
    repeat {
        m <- lm(t ~ x_mem, g)
        slope <- m$coefficients["x_mem"]
        pred <- function(v) {
            sapply(v, function(z) { t0 + slope*z })   # Predictions with the fitted slope and our own intercept
        }
        nunder <- length(which(pred(f$x_mem) > f$t))  # Underestimated points in the full dataset.
        loops = loops+1
        if (nunder/npoints >= threshold || loops >= limit) break
        g <- g[g$t>pred(g$x_mem),]  # Discard points below our regression line and start again.
    }

    ## Report some diagnostic information.  This will be seen when generate-cost-model is run.
    predicted.t <- pred(f$x_mem)
    overestimates <- which (predicted.t > f$t)
    overprediction.ratio = predicted.t[overestimates]/f$t[overestimates]
    underestimates <- which (predicted.t < f$t)
    underprediction.ratio = f$t[underestimates]/predicted.t[underestimates]

    cat (sprintf("# INFO [%s]: %d model iteration%s\n", fname, loops, ifelse(loops==1,"","s")))
    cat (sprintf(
        "# INFO [%s]: %.1f%% of predictions are underestimates. Observation exceeds prediction by a maximum factor of %.2fx (mean %.2fx).\n",
        fname, (length(underestimates)/length(f$x))*100, max(underprediction.ratio), mean(underprediction.ratio)))
    cat (sprintf(
        "# INFO [%s]: %.1f%% of predictions are overestimates. Prediction exceeds observation by a maximum factor of %.2fx (mean %.2fx).\n",
        fname, (length(overestimates)/length(f$x))*100, max(overprediction.ratio), mean(overprediction.ratio)))

    ## Adjust m's intercept; this is questionable since the rest of the model
    ## data becomes meaningless.
    m$coefficients["(Intercept)"] <- t0

    if (do.plot) {
        plot(f$x_mem,f$t, main=fname, xlab="Data size", ylab="Time (µs)")
        abline(m,col=2)
    }
    return(m)
}

modelFun <- function(path) {
    data <- get.bench.data(path)

    ## Pair the coefficients of a model together with a type tag and possibly
    ## some other data.  We return one of these to Haskell for every builtin.
    mk.result <- function(model, type, ...) {
        list(type=type, model=model, ...)
    }

    ## Look for a single entry with the given name and return the 't' value
    ## (ie, the mean execution time) for that entry.  If <name> occurs multiple
    ## times, return the mean value, and if it's not present return zero,
    ## issuing a warning in both cases
    get.mean.time <- function(fname) {
        t <- data$t[data$name == fname]
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
    discard.overhead <- function(frame) {
        fname <- frame$name[1]
        ar <- arity (fname)
        if(ar < 0) {
            stop(sprintf("ERROR: no arity information for %s\n", fname))
        }
        args.overhead <- overhead[ar]
        mean.time <- mean(frame$t)
        if (mean.time > args.overhead) {
            f <- mutate(frame,across(c("t", "t.mean.lb", "t.mean.ub"), function(x) { x - args.overhead }))
            return(f)
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
            f <- mutate(frame,across(c("t", "t.mean.lb", "t.mean.ub"), function(x) { default }))
            return(f)
        }
    }

    constantModel <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty (fname) %>%
            discard.upper.outliers () %>%
            discard.overhead ()
        m <- lm(t ~ 1, filtered)
        return (mk.result(m, "constant_cost"))
    }

   linearInX <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty (fname) %>%
            discard.overhead ()
        m <- lm(t ~ x_mem, filtered)
        return (mk.result(m, "linear_in_x"))
   }

   linearInY <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ y_mem, filtered)
        return (mk.result(m, "linear_in_y"))
   }

   linearInZ <- function (fname) {
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ z_mem, filtered)
        return (mk.result(m, "linear_in_z"))
   }

    ##### Integers #####

    addIntegerModel <- {
        fname <- "AddInteger"
        filtered <- data %>%
            filter.and.check.nonempty (fname)  %>%
            discard.overhead ()
        m <- lm(t ~ pmax(x_mem, y_mem), filtered)
        mk.result(m, "max_size")
    }
    subtractIntegerModel <- addIntegerModel

    multiplyIntegerModel <- {
        fname <- "MultiplyInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname)  %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ I(x_mem * y_mem), filtered)
        mk.result(m,"multiplied_sizes")
    }
    ## We do want I(x+y) here ^: the cost is linear, but symmetric.


    ## This is very complicated.  It's constant above the diagonal but quadratic
    ## below it.  For now we fit a crude model to the below-diagonal part and an
    ## arbitrary value above the diagonal (see CreateCostModel.hs).  Later we
    ## should find the actual mean value above the diagonal and try to fit a
    ## better model below it.  Experiments suggest that a quadratic model gives
    ## a good fit.
    divideIntegerModel <- {
        fname <- "DivideInteger"

        data1 <- data %>%  ## Data on or above diagonal: effectively constant time.
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            filter (x_mem <= y_mem) %>%
            discard.overhead ()
        constant = mean(data1$t)

        data2 <- data %>%  ## Data below diagonal
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            filter (x_mem > y_mem) %>%
            discard.overhead ()
        m <- lm(t ~ I(x_mem) + I(y_mem) + I(x_mem^2) + I(x_mem * y_mem) + I(y_mem^2), data2)

        ## Re-use the above-diagonal cost as the minimum cost below the diagonal.  See Note
        ## [Minimum values for two-variable quadratic costing functions].
        mk.result(m, "const_above_diagonal", constant=constant, minimum=constant, subtype="quadratic_in_x_and_y")
    }

    quotientIntegerModel  <- divideIntegerModel
    remainderIntegerModel <- divideIntegerModel
    modIntegerModel       <- divideIntegerModel

    ## This could possibly be made constant away from the diagonal; it's harmless
    ## to make it linear everywhere, but may overprice some comparisons a bit.
    equalsIntegerModel <- {
        fname <- "EqualsInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ pmin(x_mem, y_mem), filtered)
        mk.result(m, "min_size")
    }

    lessThanIntegerModel <- {
        fname <- "LessThanInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ pmin(x_mem, y_mem), filtered)
        mk.result(m, "min_size")
    }

    lessThanEqualsIntegerModel <- {
        fname <- "LessThanEqualsInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            filter (x_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ pmin(x_mem, y_mem), filtered)
        mk.result(m, "min_size")
    }


    ##### Bytestrings #####

    ## Note that this is symmetrical in the arguments: a new bytestring is
    ## created and the contents of both arguments are copied into it.
    appendByteStringModel <- {
        fname <- "AppendByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ I(x_mem + y_mem), filtered)
        mk.result(m, "added_sizes")
    }

    ## Depends on the size of the second argument, which has to be copied into
    ## the destination.
    consByteStringModel  <- linearInY ("ConsByteString")

    ## Bytetrings are immutable arrays with a pointer to the start and a length.
    ## SliceByteString just adjusts the pointer and length, so should be constant
    ## cost.  We've kept the linear model for compatibility reasons.
    sliceByteStringModel <- linearInZ ("SliceByteString")

    lengthOfByteStringModel <- constantModel ("LengthOfByteString")  ## Just returns a field
    indexByteStringModel    <- constantModel ("IndexByteString")     ## Constant-time array access

    ## NOTE: We could also use const_off_diagonal here, but we have to keep
    ## linear _on_diagonal for backward compatibility for the time being.
    ## See Note [Backward compatibility for costing functions].
    equalsByteStringModel <- {
        fname <- "EqualsByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            discard.overhead ()
        m <- lm(t ~ x_mem, filtered)

        constant <- min(filtered$t)
        ## FIXME.  The `constant` value above is the off-diagonal cost, which we
        ## don't collect benchmarking data for.  Collect some data and infer it.

        mk.result(m, "linear_on_diagonal", constant=constant)
    }

    lessThanByteStringModel <- {
        fname <- "LessThanByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ pmin(x_mem, y_mem), filtered)
        mk.result(m, "min_size")
    }

    lessThanEqualsByteStringModel <- lessThanByteStringModel  ## Check this!


    ###### Hashing functions #####

    sha2_256Model    <- linearInX ("Sha2_256")
    sha3_256Model    <- linearInX ("Sha3_256")
    blake2b_224Model <- linearInX ("Blake2b_224")
    blake2b_256Model <- linearInX ("Blake2b_256")
    keccak_256Model  <- linearInX ("Keccak_256")
    ripemd_160Model  <- linearInX ("Ripemd_160")

    ###### Signature verification #####

    ## VerifyEd25519Signature in fact takes three arguments, but the first and
    ## third are of fixed size so we only gather benchmarking data for
    ## different sizes of the second argument (the message being signed).
    verifyEd25519SignatureModel <- linearInY ("VerifyEd25519Signature")

    ## Similar to VerifyEd25519Signature.
    verifySchnorrSecp256k1SignatureModel <- linearInY ("VerifySchnorrSecp256k1Signature")

    ## All of the arguments of VerifyEcdsaSecp256k1Signature are of fixed size.
    ## The "message" (usually a hash of the real message) is always 32 bytes
    ## long.
    verifyEcdsaSecp256k1SignatureModel <- constantModel ("VerifyEcdsaSecp256k1Signature")


    ##### Strings #####

    appendStringModel <- {
        fname <- "AppendString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0)    %>%
            discard.overhead ()
        m <- lm(t ~ I(x_mem + y_mem), filtered)  ## Both strings are copied in full
        mk.result(m, "added_sizes")
    }

    ## NOTE: We could also use const_off_diagonal here, but we have to keep
    ## linear _on_diagonal for backward compatibility for the time being.
    ## See Note [Backward compatibility for costing functions].
    equalsStringModel <- {
        fname <- "EqualsString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem == y_mem) %>%
            discard.overhead ()
        m <- lm(t ~ x_mem, filtered)

        constant <- min(filtered$t)
        ## FIXME.  The `constant` value above is the off-diagonal cost, which
        ## we don't collect benchmarking data for.  We might want to collect
        ## some data and infer it.

        mk.result(m, "linear_on_diagonal", constant=constant)
    }

    decodeUtf8Model <- linearInX ("DecodeUtf8")
    encodeUtf8Model <- linearInX ("EncodeUtf8")

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


    ## The equalsData builtin is tricky because it uses the Eq instance for
    ## Data, which can't call costing functions for embedded Integers and Text
    ## objects.  We only have one number to measure the memory usage of a Data
    ## object and it can't disinguish between an object with lots of nodes and
    ## not much atomic data and an object with a small number of nodes each
    ## containing e.g. a large bytestring, and the comparison times for these
    ## are likely to be different.  We use the fit.fan method (defined above) to
    ## find an upper bound; this expects one-dimensional data, but fortunately
    ## our benchmark results only contain data with x_mem == y_mem, so with a
    ## bit of massaging we can still use it.  We issue a warning if the x_mem
    ## and y_mem vectors differ.

    equalsDataModel   <- {
        fname <- "EqualsData"
        filtered <- data %>% filter.and.check.nonempty(fname)
        if (!identical(filtered$x_mem, filtered$y_mem))
            cat(sprintf ("* WARNING: x_mem and y_mem differ in %s: inferred model may be inaccurate\n", fname))
        m <- fit.fan(filtered)
        v <- coefficients(m)
        names(v) <- c("(Intercept)", "pmin(x_mem, y_mem)")
        ## ^ Make it look like what the Haskell code's expecting. The space after the comma is important.
        m2 <- lm(t ~ pmin(x_mem, y_mem), filtered) # A model with the structure expected by CreateBuiltinCostModel.
        m2$coefficients <- v
        ## ^ The rest of the data in the model now becomes nonsensical, but we don't use it.
        ## FIXME: do something better.
        mk.result(m2, "min_size")
    }

    ## Data serialisation times are also non-uniform (as for equalsData).
    serialiseDataModel <- {
        fname <- "SerialiseData"
        filtered <- data %>% filter.and.check.nonempty(fname)
        m <- fit.fan(filtered)
        mk.result(m, "linear_in_x")
    }


    ##### Miscellaneous constructors #####

    mkPairDataModel     <- constantModel ("MkPairData")
    mkNilDataModel      <- constantModel ("MkNilData")
    mkNilPairDataModel  <- constantModel ("MkNilPairData")

    ##### BLS12_381 operations #####

    bls12_381_G1_addModel            <- constantModel ("Bls12_381_G1_add")
    bls12_381_G1_negModel            <- constantModel ("Bls12_381_G1_neg")
    bls12_381_G1_scalarMulModel      <- linearInX     ("Bls12_381_G1_scalarMul")
    bls12_381_G1_multiScalarMulModel <- linearInX     ("Bls12_381_G1_multiScalarMul")
    bls12_381_G1_equalModel          <- constantModel ("Bls12_381_G1_equal")
    bls12_381_G1_hashToGroupModel    <- linearInX     ("Bls12_381_G1_hashToGroup")
    bls12_381_G1_compressModel       <- constantModel ("Bls12_381_G1_compress")
    bls12_381_G1_uncompressModel     <- constantModel ("Bls12_381_G1_uncompress")
    bls12_381_G2_addModel            <- constantModel ("Bls12_381_G2_add")

    bls12_381_G2_negModel            <- constantModel ("Bls12_381_G2_neg")
    bls12_381_G2_scalarMulModel      <- linearInX     ("Bls12_381_G2_scalarMul")
    bls12_381_G2_multiScalarMulModel <- linearInX     ("Bls12_381_G2_multiScalarMul")
    bls12_381_G2_equalModel          <- constantModel ("Bls12_381_G2_equal")
    bls12_381_G2_hashToGroupModel    <- linearInX     ("Bls12_381_G2_hashToGroup")
    bls12_381_G2_compressModel       <- constantModel ("Bls12_381_G2_compress")
    bls12_381_G2_uncompressModel     <- constantModel ("Bls12_381_G2_uncompress")
    bls12_381_millerLoopModel        <- constantModel ("Bls12_381_millerLoop")
    bls12_381_mulMlResultModel       <- constantModel ("Bls12_381_mulMlResult")
    bls12_381_finalVerifyModel       <- constantModel ("Bls12_381_finalVerify")

    ##### Bitwise operations #####

    ## If we give `integerToByteString` a width argument w > 0 and a small
    ## integer n to be converted, the cost is based only on the size of n even
    ## though w could be considerably larger and some work will be required to
    ## pad the output to width w.  Experiments show that the padding cost is
    ## negligible in comparison to the conversion cost, so it's safe to base the
    ## cost purely on the size of n.
    integerToByteStringModel <- {
        fname <- "IntegerToByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname)
        m <- lm(t ~ I(z_mem) + I(z_mem^2), filtered)
        mk.result(m, "quadratic_in_z")
    }

    byteStringToIntegerModel <- {
        fname <- "ByteStringToInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname)
        m <- lm(t ~ I(y_mem) + I(y_mem^2), filtered)
        mk.result(m, "quadratic_in_y")
    }

    andByteStringModel <- {
        fname <- "AndByteString"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ y_mem + z_mem, filtered)
        mk.result(m, "linear_in_y_and_z")
    }
    orByteStringModel         <- andByteStringModel
    xorByteStringModel        <- andByteStringModel

    complementByteStringModel <- linearInX ("ComplementByteString")
    readBitModel              <- constantModel ("ReadBit")
    writeBitsModel            <- linearInY ("WriteBits")
    ## ^ The Y value here is the length of the list of positions because we use ListCostedByLength
    ## in the relevant costing benchmark.
    replicateByteModel        <- linearInX ("ReplicateByte")
    shiftByteStringModel      <- linearInX ("ShiftByteString")
    rotateByteStringModel     <- linearInX ("RotateByteString")
    countSetBitsModel         <- linearInX ("CountSetBits")
    findFirstSetBitModel      <- linearInX ("FindFirstSetBit")


    expModIntegerModel    <- {
        fname <- "ExpModInteger"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter(x_mem > 0 & y_mem > 0) %>%
            discard.overhead ()
        m <- lm(t ~ I(y_mem*z_mem) + I(y_mem*z_mem^2), filtered)
        mk.result(m, "exp_mod_cost")
    }

    dropListModel <- linearInX ("DropList")

    ## Arrays
    lengthOfArrayModel        <- constantModel ("LengthOfArray")
    listToArrayModel          <- linearInX ("ListToArray")
    indexArrayModel           <- constantModel ("IndexArray")

    ## Values

    # Z wrapped with `Logarithmic . ValueOuterOrMaxInner`
    lookupCoinModel           <- linearInZ ("LookupCoin")    

    ## X wrapped with `ValueMaxDepth` (sum of logarithmic sizes)
    ## Y wrapped with `ValueTotalSize` (contained value size)
    valueContainsModel <- {
        fname <- "ValueContains"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            discard.overhead ()
        m <- lm(t ~ I(x_mem * y_mem), filtered)
        mk.result(m, "multiplied_sizes")
    }         

    ## Really linearInX, but we want to restrict the X values for the time being
    ## FIXME: make the benchmark inputs a bit smaller.  They currently go up to
    ## a size that's much bigger than we're ever likely to encounter.
    valueDataModel <-  {
        fname <- "ValueData"
        filtered <- data %>%
            filter.and.check.nonempty(fname) %>%
            filter (x_mem < 50000) %>%
            discard.overhead ()
        m <- lm(t ~ x_mem, filtered)
        mk.result(m, "linear_in_x")
    }

    ## X wrapped with DataNodeCount
    unValueDataModel          <- linearInX ("UnValueData")

    ##### Models to be returned to Haskell #####

    models.for.adjustment <-
        list (
        addIntegerModel                      = addIntegerModel,
        subtractIntegerModel                 = subtractIntegerModel,
        multiplyIntegerModel                 = multiplyIntegerModel,
        equalsIntegerModel                   = equalsIntegerModel,
        lessThanIntegerModel                 = lessThanIntegerModel,
        lessThanEqualsIntegerModel           = lessThanEqualsIntegerModel,
        appendByteStringModel                = appendByteStringModel,
        consByteStringModel                  = consByteStringModel,
        sliceByteStringModel                 = sliceByteStringModel,
        lengthOfByteStringModel              = lengthOfByteStringModel,
        indexByteStringModel                 = indexByteStringModel,
        equalsByteStringModel                = equalsByteStringModel,
        lessThanByteStringModel              = lessThanByteStringModel,
        lessThanEqualsByteStringModel        = lessThanEqualsByteStringModel,
        sha2_256Model                        = sha2_256Model,
        sha3_256Model                        = sha3_256Model,
        blake2b_224Model                     = blake2b_224Model,
        blake2b_256Model                     = blake2b_256Model,
        keccak_256Model                      = keccak_256Model,
        verifyEd25519SignatureModel          = verifyEd25519SignatureModel,
        verifyEcdsaSecp256k1SignatureModel   = verifyEcdsaSecp256k1SignatureModel,
        verifySchnorrSecp256k1SignatureModel = verifySchnorrSecp256k1SignatureModel,
        appendStringModel                    = appendStringModel,
        equalsStringModel                    = equalsStringModel,
        encodeUtf8Model                      = encodeUtf8Model,
        decodeUtf8Model                      = decodeUtf8Model,
        ifThenElseModel                      = ifThenElseModel,
        chooseUnitModel                      = chooseUnitModel,
        traceModel                           = traceModel,
        fstPairModel                         = fstPairModel,
        sndPairModel                         = sndPairModel,
        chooseListModel                      = chooseListModel,
        mkConsModel                          = mkConsModel,
        headListModel                        = headListModel,
        tailListModel                        = tailListModel,
        nullListModel                        = nullListModel,
        chooseDataModel                      = chooseDataModel,
        constrDataModel                      = constrDataModel,
        mapDataModel                         = mapDataModel,
        listDataModel                        = listDataModel,
        iDataModel                           = iDataModel,
        bDataModel                           = bDataModel,
        unConstrDataModel                    = unConstrDataModel,
        unMapDataModel                       = unMapDataModel,
        unListDataModel                      = unListDataModel,
        unIDataModel                         = unIDataModel,
        unBDataModel                         = unBDataModel,
        equalsDataModel                      = equalsDataModel,
        mkPairDataModel                      = mkPairDataModel,
        mkNilDataModel                       = mkNilDataModel,
        mkNilPairDataModel                   = mkNilPairDataModel,
        serialiseDataModel                   = serialiseDataModel,
        bls12_381_G1_addModel                = bls12_381_G1_addModel,
        bls12_381_G1_negModel                = bls12_381_G1_negModel,
        bls12_381_G1_scalarMulModel          = bls12_381_G1_scalarMulModel,
        bls12_381_G1_multiScalarMulModel     = bls12_381_G1_multiScalarMulModel,
        bls12_381_G1_equalModel              = bls12_381_G1_equalModel,
        bls12_381_G1_hashToGroupModel        = bls12_381_G1_hashToGroupModel,
        bls12_381_G1_compressModel           = bls12_381_G1_compressModel,
        bls12_381_G1_uncompressModel         = bls12_381_G1_uncompressModel,
        bls12_381_G2_addModel                = bls12_381_G2_addModel,
        bls12_381_G2_negModel                = bls12_381_G2_negModel,
        bls12_381_G2_scalarMulModel          = bls12_381_G2_scalarMulModel,
        bls12_381_G2_multiScalarMulModel     = bls12_381_G2_multiScalarMulModel,
        bls12_381_G2_equalModel              = bls12_381_G2_equalModel,
        bls12_381_G2_hashToGroupModel        = bls12_381_G2_hashToGroupModel,
        bls12_381_G2_compressModel           = bls12_381_G2_compressModel,
        bls12_381_G2_uncompressModel         = bls12_381_G2_uncompressModel,
        bls12_381_millerLoopModel            = bls12_381_millerLoopModel,
        bls12_381_mulMlResultModel           = bls12_381_mulMlResultModel,
        bls12_381_finalVerifyModel           = bls12_381_finalVerifyModel,
        integerToByteStringModel             = integerToByteStringModel,
        byteStringToIntegerModel             = byteStringToIntegerModel,
        andByteStringModel                   = andByteStringModel,
        orByteStringModel                    = orByteStringModel,
        xorByteStringModel                   = xorByteStringModel,
        complementByteStringModel            = complementByteStringModel,
        readBitModel                         = readBitModel,
        writeBitsModel                       = writeBitsModel,
        replicateByteModel                   = replicateByteModel,
        shiftByteStringModel                 = shiftByteStringModel,
        rotateByteStringModel                = rotateByteStringModel,
        countSetBitsModel                    = countSetBitsModel,
        findFirstSetBitModel                 = findFirstSetBitModel,
        ripemd_160Model                      = ripemd_160Model,
        expModIntegerModel                   = expModIntegerModel,
        dropListModel                        = dropListModel,
        lengthOfArrayModel                   = lengthOfArrayModel,
        listToArrayModel                     = listToArrayModel,
        indexArrayModel                      = indexArrayModel,
        lookupCoinModel                      = lookupCoinModel,
        valueContainsModel                   = valueContainsModel,
        valueDataModel                       = valueDataModel,
        unValueDataModel                     = unValueDataModel
        )

    ## The integer division functions have a complex costing behaviour that requires some negative
    ## coefficients to get accurate results. Because of this they are excluded from adjustModels:
    ## the Haskell code receives the raw model and takes care of the (unlikely) case when a negative
    ## value is returned itself (using a minimm value returned from R as an extra parameter).  Any
    ## other builtins which need a non-monotonic costing function should be treated similarly.

    unadjusted.models <- list (
        divideIntegerModel                   = divideIntegerModel,
        quotientIntegerModel                 = quotientIntegerModel,
        remainderIntegerModel                = remainderIntegerModel,
        modIntegerModel                      = modIntegerModel
    )

    return(c(adjustModels(models.for.adjustment), unadjusted.models))
}
