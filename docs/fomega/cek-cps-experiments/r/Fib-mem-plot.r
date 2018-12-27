title <- "Fib (memory)"

masterdata <- read.table("master-times-Fib", header=T)
recdata  <- read.table("recursive-times-Fib", header=T)
cpsdata <- read.table("cps-times-Fib", header=T)
origdata <- read.table("orig-times-Fib", header=T)

allmem <-  c(masterdata$mem, recdata$mem, cpsdata$mem, origdata$mem)
ylim <- c(min(allmem)/1024, max(allmem/1024)+10)

start <- function(fr,col) {  # Just to make it easier to plot biggest thing first by Trial and error
    plot  (fr$n,fr$mem/1024, col=col, pch=20, main=title, xlab = "n", ylab ="Memory (MB)", ylim=ylim)
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

start (cpsdata, cpscol)
draw  (masterdata,mastercol)
draw  (recdata,reccol)
draw  (origdata, origcol)

    
legend(x="topleft", inset=.05, legend=c("master","recursive", "CPS", "Original CEK machine"), col=c(mastercol, reccol, cpscol, origcol), lty=1, lw=2)
