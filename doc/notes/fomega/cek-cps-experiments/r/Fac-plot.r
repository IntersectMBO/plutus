title = "Fac (time)"

masterdata <- read.table("master-times-Fac", header=T)
recdata  <- read.table("recursive-times-Fac", header=T)
cpsdata <- read.table("cps-times-Fac", header=T)
origdata <- read.table("orig-times-Fac", header=T)



all <-  c(masterdata$usr+masterdata$sys, recdata$usr+recdata$sys, cpsdata$usr+cpsdata$sys, origdata$usr+origdata$sys)
ylim <- c(min(all), max(all))

start <- function(fr,col) {
    plot  (fr$n,fr$usr+fr$sys, col=col, pch=20, main=title, xlab = "n", ylab = "Time (s)", ylim=ylim)
    lines (fr$n,fr$usr+fr$sys, col=col, pch=20)
}

draw <- function(fr,col) {
    points (fr$n,fr$usr+fr$sys, col=col, pch=20)
    lines  (fr$n,fr$usr+fr$sys, col=col, pch=20)
}

mastercol="gold"
reccol="darkolivegreen3"
cpscol="blue"
origcol="darkmagenta"


start  (recdata,reccol)
draw (origdata, origcol)
draw  (masterdata,mastercol)
draw  (cpsdata, cpscol)

    
legend(x="topleft", inset=.05, legend=c("master","recursive", "CPS", "Original CEK machine"), col=c(mastercol, reccol, cpscol, origcol), lty=1, lw=2)
