title <- "Tri (memory)"

ckdata <- read.table("CK-times-tri", header=T)
cekdata  <- read.table("CEK-times-tri", header=T)
ldata <- read.table("L-times-tri", header=T)
ydata <- read.table("Y-times-tri", header=T)

start <- function(fr,col) {  # Just to make it easier to plot biggest thing first by trial and error
    plot  (fr$n,fr$mem/1024, col=col, pch=20, main=title, xlab = "n", ylab ="Memory (MB)")
    lines (fr$n,fr$mem/1024, col=col, pch=20)
}

draw <- function(fr,col) {
    points (fr$n,fr$mem/1024, col=col, pch=20)
    lines  (fr$n,fr$mem/1024, col=col, pch=20)
}

ckcol="gold"
cekcol="darkolivegreen3"
lcol="blue"
ycol="darkmagenta"

start (ckdata, ckcol)
draw  (cekdata,cekcol)
draw  (ldata, lcol)
draw  (ydata, ycol)

    
legend(x="topleft", inset=.05, legend=c("CK machine","CEK machine", "L machine", "L machine (Y combinator)"), col=c(ckcol, cekcol, lcol, ycol), lty=1, lw=2)
