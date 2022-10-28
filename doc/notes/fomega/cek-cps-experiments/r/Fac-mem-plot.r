title <- "Fac (memory)"

masterdata <- read.table("master-times-Fac", header=T)
recdata <- read.table("recursive-times-Fac", header=T)
cpsdata <- read.table("cps-times-Fac", header=T)
origdata <- read.table("orig-times-Fac", header=T)

allmem <-  c(masterdata$mem, recdata$mem, cpsdata$mem, origdata$mem)
ylim <- c(min(allmem)/1024, max(allmem/1024))


start <- function(fr,col) {  # Just to make it easier to plot biggest thing first by Trial and error
    plot  (fr$n,fr$mem/1024, col=col, pch=20, main=title, xlab = "n", ylab ="Memory (MB)", xlim = c(0,max(masterdata$n)), ylim=ylim)
    lines (fr$n,fr$mem/1024, col=col, pch=20)
}

draw <- function(fr,col) {
    points (fr$n,fr$mem/1024, col=col, pch=20)
    lines  (fr$n,fr$mem/1024, col=col, pch=20)
}

mastercol="gold"
reccol="darkolivegreen3"
cpscol="blue"
origcol="darkmagenta"

start (origdata, origcol)
draw  (masterdata,mastercol)
draw  (recdata,reccol)
draw  (cpsdata, cpscol)

    
legend(x="topleft", inset=.05, legend=c("master","recursive", "CPS", "Original CEK machine"), col=c(mastercol, reccol, cpscol, origcol), lty=1, lw=2)
