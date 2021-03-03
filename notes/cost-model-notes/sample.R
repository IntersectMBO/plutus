# An example of how to produce 3D OpenGl plots of the benchmarking
# output using the rgl library (using old-fashioned R).
#
# The data used below was stored in a frame obtained by editing benching.csv to
# make it a bit easier to use interactively.  It starts like this:
#
#   name x y z zlb zub Stddev Stddevlb Stddevub
#   AddInteger 0 0  1.3243758200107631e-5  1.3218696780148429e-5  1.3317044630132778e-5  1.2650898075066926e-7  3.884518488170315e-8  2.439352295888436e-7
#   AddInteger 0 0  1.3383234306420691e-5  1.3377188501878156e-5  1.33910446176838e-5  2.320143512159567e-8  1.7353723480572102e-8  3.735791154823481e-8
#   ...

# Here's a sample of the sort of thing I did to get the plots (extracted from .Rhistory)

require(rgl)
frame <- "~/plutus/plutus/plutus-core/cost-model/budgeting-bench/csvs/benching.frame"
h <- read.table(frame, header=T, stringsAsFactors=F)
h$z <- h$z * 1e6                                          # Rescale: should really have done this in the input file.
f <- h[h$name=="DivideInteger" & h$x < 2000 &h$y < 2000,] # filter data of interest
plot3d(f$x,f$y,f$z,type="s", col=4, r=50)                 # r = radius of balls
#  <Move the image about with the mouse to get a good viewpoint>
rgl.snapshot("divide.png")                                # save image in a png

# PDF images are better for TeX since they rescale better than PNGs.
# We're supposed to be able to get a PDF by saying
#      rgl.postscript ("divide.pdf", fmt="pdf")
# but that was extremely slow and produced a massive file.  
#
# This is only problematic for the OpenGL plots produced by rgl.
# For standard 2D plots in R the usual methods work well: eg 
#      pdf ("output.pdf")
#      <run your plot command>
#      dev.off()
#
