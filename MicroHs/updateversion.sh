MP=paths/Paths_MicroHs.hs
mv $MP $MP.bak
grep -v '^version =' $MP.bak > $MP
grep '^version:' MicroHs.cabal | sed -e 's/: */ = makeVersion [/' -e 's/\./,/g' -e 's/$/]/' >> $MP
#
MK=Makefile
mv $MK $MK.bak
vers=`grep '^version:' MicroHs.cabal | sed -e 's/version: *//'`
hvers=`echo $vers | sed 's/\./,/g'`
#echo $vers
sed -e "s/^VERSION=.*/VERSION=$vers/" -e "s/^HVERSION=.*/HVERSION=$hvers/" $MK.bak > $MK
LCB=lib/libs.cabal
mv $LCB $LCB.bak
sed -e "s/^version: .*/version:        $vers/" $LCB.bak > $LCB
SI=lib/System/Info.hs
mv $SI $SI.bak
grep -v '^fullCompilerVersion =' $SI.bak > $SI
grep '^version:' MicroHs.cabal | sed -e 's/version: */fullCompilerVersion = makeVersion [/' -e 's/\./,/g' -e 's/$/]/' >> $SI
