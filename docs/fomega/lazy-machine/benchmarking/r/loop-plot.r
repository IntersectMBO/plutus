title <- "Loop (time)"

ckdata <- read.table("CK-times-loop", header=T)
cekdata  <- read.table("CEK-times-loop", header=T)
ldata <- read.table("L-times-loop", header=T)
ydata <- read.table("Y-times-loop", header=T)

start <- function(fr,col) {  
    plot  (fr$n,fr$usr+fr$sys, col=col, pch=20, main=title, xlab = "n", ylab = "Time (s)")
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

start (ckdata, ckcol)
draw  (cekdata, cekcol)
draw  (ldata, lcol)
draw  (ydata, ycol)

    
legend(x="topleft", inset=.05, legend=c("CK machine","CEK machine", "L machine", "L machine (Y combinator)"), col=c(ckcol, cekcol, lcol, ycol), lty=1, lw=2)
