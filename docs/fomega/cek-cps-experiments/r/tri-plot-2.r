title <- "Tri (time)"


origdata  <- read.table("recursive-times-Tri", header=T)
cpsdata <- read.table("cps-times-Tri", header=T)
recdata <- read.table("orig-times-Tri", header=T)

all <-  c(recdata$usr+recdata$sys, cpsdata$usr+cpsdata$sys, origdata$usr+origdata$sys)
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


start  (recdata, reccol)
draw  (cpsdata, cpscol)
draw  (origdata, origcol)
    
legend(x="topleft", inset=.05, legend=c("recursive", "CPS", "Original CEK machine"), col=c(reccol, cpscol, origcol), lty=1, lw=2)
