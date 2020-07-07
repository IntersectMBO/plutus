title = "Fac (time)"

ckdata <- read.table("CK-times-fac", header=T)
cekdata  <- read.table("CEK-times-fac", header=T)
ldata <- read.table("L-times-fac", header=T)
ydata <- read.table("Y-times-fac", header=T)

start <- function(fr,col) {
    plot  (fr$n,fr$usr+fr$sys, col=col, pch=20, main=title, xlab = "n", ylab = "Time (s)", xlim = c(0,max(ckdata$n))) ## Ran out of memory
    lines (fr$n,fr$usr+fr$sys, col=col, pch=20)
}

draw <- function(fr,col) {
    points (fr$n,fr$usr+fr$sys, col=col, pch=20)
    lines  (fr$n,fr$usr+fr$sys, col=col, pch=20)
}

ckcol="gold"
cekcol="darkolivegreen3"
lcol="blue"
ycol="darkmagenta"


start (ydata, ycol)
draw  (ckdata,ckcol)
draw  (cekdata,cekcol)
draw  (ldata, lcol)

    
legend(x="topleft", inset=.05, legend=c("CK machine","CEK machine", "L machine", "L machine (Y combinator)"), col=c(ckcol, cekcol, lcol, ycol), lty=1, lw=2)
