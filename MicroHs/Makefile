# Define these 3 lines to use GMP for Integer.
# For MacOS with homebrew:
#MHSGMPCCFLAGS=-DWANT_GMP=1
#MHSGMPCCLIBS= -L/opt/homebrew/lib -lgmp -I/opt/homebrew/include
#MHSGMP=-ilib/gmp
#MCABALGMP=-fgmp
#
# installation prefix
PREFIX=/usr/local
# Unix-like system, 64 bit words
CONF=unix-64
#
# Using GCC enables global register variables on ARM64, which gives a 5-10% speedup.
#CC=gcc-14
CCWARNS= -Wall
CCOPTS= -O3
CCLIBS= -lm
CCSANITIZE= -fsanitize=undefined -fsanitize=address -fsanitize=pointer-compare -fsanitize=pointer-subtract
CCEVAL= $(CC) $(CCWARNS) $(CCOPTS) $(MHSGMPCCFLAGS) -Isrc/runtime src/runtime/eval-$(CONF).c $(CCLIBS) $(MHSGMPCCLIBS)
#
GHC= ghc
GHCINCS= -ighc -isrc -ipaths
GHCWARNS= -Wall -Wno-unrecognised-warning-flags -Wno-x-partial -Wno-deprecations
GHCOPTS= -O
GHCEXTS= -XScopedTypeVariables -XTypeSynonymInstances -XMultiParamTypeClasses -XFlexibleInstances
GHCPKGS= -package mtl -package pretty -package haskeline -package process -package time -package ghc-prim -package containers -package deepseq -package directory -package text -package bytestring -package filepath -package array
GHCTOOL= # -F -pgmF Tools/convertX.sh
GHCOUTDIR= ghc-out
GHCOUT= -outputdir $(GHCOUTDIR)
GHCPROF= # -prof -fprof-late #-prof -fprof-auto
GHCFLAGS= $(GHCEXTS) $(GHCINCS) $(GHCWARNS) $(GHCOPTS) $(GHCTOOL) $(GHCPKGS) $(GHCOUT) $(GHCPROF) -main-is MicroHs.Main
#
# Hugs
HUGS= runhugs
FFIHUGS= ffihugs
HUGSINCS= '+Phugs:mhs:src:paths:{Hugs}/packages/*:hugs/obj' -98 +o +w

#
EMCC=emcc
EMCCFLAGS=-sALLOW_MEMORY_GROWTH -sTOTAL_STACK=5MB -sNODERAWFS -sSINGLE_FILE -DUSE_SYSTEM_RAW
#
MHSINCNP= -i $(MHSGMP) -imhs -isrc -ilib
MHSINC=$(MHSINCNP) -ipaths 
MAINMODULE=MicroHs.Main
#
.PHONY:	clean bootstrap install ghcgen newmhs newmhsz cachelib timecompile exampletest cachetest runtest runtestmhs everytest everytestmhs nfibtest info install minstall installmsg

all:	bin/mhs bin/cpphs bin/mcabal

targets.conf:
	echo "[default]"                     > targets.conf
	echo cc = \"$(CC)\"                 >> targets.conf
	echo ccflags = \"$(MHSGMPCCFLAGS)\" >> targets.conf
	echo cclibs = \"$(MHSGMPCCLIBS)\"   >> targets.conf
	echo conf = \"$(CONF)\"             >> targets.conf
	echo ''                             >> targets.conf
	echo "[emscripten]"                 >> targets.conf
	echo cc = \"$(EMCC)\"               >> targets.conf
	echo ccflags = \"$(EMCCFLAGS)\"     >> targets.conf
	echo conf = \"$(CONF)\"             >> targets.conf

newmhs:	ghcgen targets.conf
	$(CCEVAL) generated/mhs.c -o bin/mhs
	$(CC) $(CCWARNS) $(MHSGMPCCFLAGS) -g -Isrc/runtime src/runtime/eval-$(CONF).c $(CCLIBS) generated/mhs.c $(MHSGMPCCLIBS) -o bin/mhsgdb

newmhsz:	newmhs
	rm generated/mhs.c
	make generated/mhs.c

sanitizemhs:	ghcgen targets.conf
	$(CCEVAL) $(CCSANITIZE) generated/mhs.c -o bin/mhssane

# Compile mhs from distribution, with C compiler
bin/mhs:	src/runtime/*.c src/runtime/*.h targets.conf #generated/mhs.c
	@mkdir -p bin
	$(CCEVAL) generated/mhs.c -o bin/mhs

# Compile cpphs from distribution, with C compiler
bin/cpphs:	src/runtime/*.c src/runtime/config*.h #generated/cpphs.c
	@mkdir -p bin
	$(CCEVAL) generated/cpphs.c -o bin/cpphs

# Compile mcabal from distribution, with C compiler
bin/mcabal:	src/runtime/*.c src/runtime/config*.h #generated/mcabal.c
	@mkdir -p bin
	$(CCEVAL) generated/mcabal.c -o bin/mcabal

# Compile combinator evaluator
bin/mhseval:	src/runtime/*.c src/runtime/config*.h
	@mkdir -p bin
	$(CCEVAL) src/runtime/comb.c -o bin/mhseval
	size bin/mhseval

bin/mhsevalgdb:	src/runtime/*.c src/runtime/config*.h
	@mkdir -p bin
	$(CC) $(CCWARNS) $(MHSGMPCCFLAGS) -g src/runtime/eval-$(CONF).c $(CCLIBS) src/runtime/comb.c $(MHSGMPCCLIBS) -o bin/mhsevalgdb

bin/mhsevalsane:	src/runtime/*.c src/runtime/config*.h
	@mkdir -p bin
	$(CCEVAL) $(CCSANITIZE) src/runtime/comb.c -o bin/mhsevalsane

# Compile mhs with ghc
bin/gmhs:	src/*/*.hs ghc/*.hs ghc/*/*.hs ghc/*/*/*.hs
	@mkdir -p bin
	$(GHC) $(GHCFLAGS) $(MAINMODULE) -o bin/gmhs

# Compile mhs with ghc, with code coverage
bin/cmhs:	src/*/*.hs ghc/*.hs ghc/*/*.hs
	@mkdir -p bin
	$(GHC) $(GHCFLAGS) -fhpc $(MAINMODULE) -o bin/cmhs

# Generate distribution C file
generated/mhs.c:	bin/mhs src/*/*.hs
	@mkdir -p generated
	bin/mhs -z $(MHSINC) $(MAINMODULE) -ogenerated/mhs.c

ghcgen:	bin/gmhs src/*/*.hs lib/*.hs lib/*/*.hs lib/*/*/*.hs
	bin/gmhs $(MHSINC) $(MAINMODULE) -ogenerated/mhs.c

# This doesn't keep MicroCabal updated.  I'm not sure how to do it
#generated/mcabal.c: MicroCabal/.git
#	bin/mhs -z -iMicroCabal/src -ilib -ogenerated/mcabal.c MicroCabal.Main
#
#MicroCabal/.git:
#	git submodule update --init --depth 1 MicroCabal
generated/mcabal.c:
	bin/mhs -z -i../MicroCabal/src -ilib -ogenerated/mcabal.c MicroCabal.Main

# Flags to read local file system, generate a single .js file, and to avoid ioctl()
mhs.js:	src/*/*.hs src/runtime/*.[ch] targets.conf
	bin/mhs $(MHSINC) -temscripten $(MAINMODULE) -o mhs.js

# Make sure boottrapping works
bootstrap:	bin/mhs-stage2
	@echo "*** copy stage2 to bin/mhs"
	cp bin/mhs-stage2 bin/mhs
	cp generated/mhs-stage2.c generated/mhs.c 

# Build stage1 compiler with existing compiler
bin/mhs-stage1:	bin/mhs src/*/*.hs
	@mkdir -p generated
	@echo "*** Build stage1 compiler, using bin/mhs"
	bin/mhs -z $(MHSINC) $(MAINMODULE) -ogenerated/mhs-stage1.c
	$(CCEVAL) generated/mhs-stage1.c -o bin/mhs-stage1

# Build stage2 compiler with stage1 compiler, and compare
bin/mhs-stage2:	bin/mhs-stage1 src/*/*.hs
	@mkdir -p generated
	@echo "*** Build stage2 compiler, with stage1 compiler"
	bin/mhs-stage1 -z $(MHSINC) $(MAINMODULE) -ogenerated/mhs-stage2.c
	cmp generated/mhs-stage1.c generated/mhs-stage2.c
	@echo "*** stage2 equal to stage1"
	$(CCEVAL) generated/mhs-stage2.c -o bin/mhs-stage2

# Fetch cpphs submodule
cpphssrc/malcolm-wallace-universe/.git:
	git submodule update --init --depth 1 cpphssrc/malcolm-wallace-universe

# Use this cpphs for bootstrapping
USECPPHS=bin/cpphs

bootstrapcpphs: bin/mhs cpphssrc/malcolm-wallace-universe/.git
	MHSCPPHS=$(USECPPHS) bin/mhs -z -XCPP '-DMIN_VERSION_base(x,y,z)=((x)<4||(x)==4&&(y)<19||(x)==4&&(y)==19&&(z)<=1)' -icpphscompat -icpphssrc/malcolm-wallace-universe/polyparse-1.12/src -icpphssrc/malcolm-wallace-universe/cpphs-1.20.9 cpphssrc/malcolm-wallace-universe/cpphs-1.20.9/cpphs.hs -ogenerated/cpphs.c

# Run test examples with ghc-compiled compiler
runtest:	bin/mhseval bin/gmhs tests/*.hs
	cd tests; make alltest

# Run test examples with mhs-compiled compiler
runtestmhs: bin/mhseval bin/mhs
	cd tests; make MHS=../bin/mhs cache; make MHS="../bin/mhs +RTS -H4M -RTS -CR" info test errtest

# Run test examples with sanitized mhs-compiled compiler
runtestsan: bin/mhsevalsane sanitizemhs
	cd tests; make MHS="../bin/mhssane +RTS -H4M -RTS -CW" cache
	cd tests; make MHS="../bin/mhssane +RTS -H4M -RTS -CR" EVAL="../bin/mhsevalsane +RTS -H1M -RTS" info test errtest

runtestgsan: bin/mhsevalsane bin/gmhs
	cd tests; make EVAL="../bin/mhsevalsane +RTS -H1M -RTS" info test errtest

# Run test examples going via JavaScript
runtestemscripten: bin/mhseval bin/mhs bin/cpphs
	cd tests; make MHS=../bin/mhs cache; MHSDIR=.. make MHS="../bin/mhs -CR -temscripten -oout.js" EVAL="node out.js" info test errtest


# Compress the binary (broken on MacOS)
bin/umhs: bin/mhs
	rm -f bin/umhs
	upx -q -q -obin/umhs bin/mhs

#
timecompile: bin/mhs
	@date
	@git rev-parse HEAD
	time bin/mhs +RTS -v -RTS $(MHSINC) $(MAINMODULE)

#
timecachecompile: bin/mhs
	@-rm -f .mhscache
	time bin/mhs +RTS -v -RTS -CW AllOfLib
	time bin/mhs +RTS -v -RTS -CR -s $(MHSINC) $(MAINMODULE)

#
timemhscompile:
	@date
	@git rev-parse HEAD
	time mhs +RTS -v -RTS -z -imhs -isrc -ipaths $(MAINMODULE)

timegmhscompile:
	@date
	@git rev-parse HEAD
	time bin/gmhs -imhs -isrc -ipaths $(MAINMODULE)

timeghccompile:
	@date
	@git rev-parse HEAD
	time $(GHC) -fforce-recomp $(GHCFLAGS) -O0 $(MAINMODULE) -o bin/gmhs

#
cachelib:
	@-rm -f .mhscache
	bin/mhs -CW AllOfLib

#
clean:
	rm -rf src/*/*.hi src/*/*.o *.comb *.js *.tmp *~ bin/* a.out $(GHCOUTDIR) Tools/*.o Tools/*.hi dist-newstyle generated/*-stage* .mhscache targets.conf .mhscache dist-mcabal Interactive.hs .mhsi
	cd tests; make clean
	-cabal clean
	-git submodule deinit cpphssrc/malcolm-wallace-universe
	-git submodule deinit MicroCabal

oldinstall:
	mkdir -p $(PREFIX)/bin
	cp bin/mhs $(PREFIX)/bin
	-cp bin/cpphs $(PREFIX)/bin
	mkdir -p $(PREFIX)/lib/mhs/src/runtime
	cp -r lib $(PREFIX)/lib/mhs
	cp src/runtime/* $(PREFIX)/lib/mhs/src/runtime
	cp targets.conf $(PREFIX)/lib/mhs/targets.conf
	@echo "***"
	@echo "*** Installation complete"
	@echo "*** Set environment variable MHSDIR to $(PREFIX)/lib/mhs"
	@echo "***"

everytest:	newmhs bin/cpphs runtest exampletest cachetest bootcombtest nfibtest info

everytestmhs:	bin/mhs bin/cpphs bin/mhseval exampletest cachetest bootstrap runtestmhs nfibtest info

bootcombtest:	bin/gmhs bin/mhseval
	bin/gmhs $(MHSINC) -ogmhs.comb $(MAINMODULE)
	bin/mhseval +RTS -v -rgmhs.comb -RTS $(MHSINC) -omhs.comb $(MAINMODULE)
	cmp gmhs.comb mhs.comb

exampletest:	bin/mhs bin/mhseval Example.hs
	bin/mhs -r Example
	bin/mhs Example && bin/mhseval
	bin/mhs Example -oEx && ./Ex && rm Ex

examplejs: bin/mhs Example.hs
	bin/mhs -temscripten Example -oEx.js
	node Ex.js
	rm Ex.js

info:	bin/mhs
	bin/mhs -r -itests Info

cachetest:	bin/mhs bin/cpphs bin/mhseval Example.hs
	rm -f .mhscache
	bin/mhs -CW AllOfLib
	bin/mhs -CR Example && bin/mhseval
	bin/mhs +RTS -v -RTS $(MHSINC) -CR $(MAINMODULE)
	rm -f .mhscache

nfibtest: bin/mhs bin/mhseval
	bin/mhs -itests Nfib && bin/mhseval

######

VERSION=0.13.2.0
HVERSION=0,13,2,0
MCABAL=$(HOME)/.mcabal
MCABALMHS=$(MCABAL)/mhs-$(VERSION)
MDATA=$(MCABALMHS)/packages/mhs-$(VERSION)/data
MRUNTIME=$(MDATA)/src/runtime
MCABALBIN=$(MCABAL)/bin
MDIST=dist-mcabal
BASE=base-$(VERSION)
BASEMODULES=Control.Applicative Control.Arrow Control.Category Control.DeepSeq Control.Error Control.Exception Control.Exception.Base Control.Monad Control.Monad.Fail Control.Monad.Fix Control.Monad.IO.Class Control.Monad.ST Control.Monad.Zip Data.Array Data.Bifoldable Data.Bifunctor Data.Bitraversable Data.Bits Data.Bool Data.Bounded Data.ByteString Data.Char Data.Complex Data.Constraint Data.Data Data.Double Data.Dynamic Data.Either Data.Enum Data.Eq Data.Fixed Data.Float Data.FloatW Data.Floating Data.Foldable Data.Foldable1 Data.Fractional Data.Function Data.Functor Data.Functor.Classes Data.Functor.Compose Data.Functor.Const Data.Functor.Contravariant Data.Functor.Identity Data.Functor.Product Data.Functor.Sum Data.Hashable Data.IOArray Data.IORef Data.Int Data.Integer Data.Integral Data.Ix Data.Kind Data.List Data.List.NonEmpty Data.Maybe Data.Monoid Data.Num Data.Ord Data.Proxy Data.Ratio Data.Real Data.RealFloat Data.RealFrac Data.Records Data.STRef Data.Semigroup Data.String Data.Text Data.Traversable Data.Tuple Data.Tuple.Instances Data.Type.Equality Data.TypeLits Data.Typeable Data.Version Data.Void Data.Word Data.ZipList Debug.Trace Foreign Foreign.C Foreign.C.Error Foreign.C.String Foreign.C.Types Foreign.ForeignPtr Foreign.Marshal Foreign.Marshal.Alloc Foreign.Marshal.Array Foreign.Marshal.Error Foreign.Marshal.Utils Foreign.Ptr Foreign.Storable GHC.Generics GHC.Stack GHC.Types Language.Haskell.TH.Syntax Mhs.Builtin Numeric Numeric.FormatFloat Numeric.Natural Prelude System.Cmd System.Console.GetOpt System.Compress System.Directory System.Environment System.Exit System.IO System.IO.Error System.IO.MD5 System.IO.PrintOrRun System.IO.Serialize System.IO.TimeMilli System.IO.Unsafe System.Info System.Process Text.Printf Text.ParserCombinators.ReadP Text.ParserCombinators.ReadPrec Text.Read Text.Read.Lex Text.Show Unsafe.Coerce

$(MCABALBIN)/mhs: bin/mhs src/runtime/*.[ch] targets.conf $(MDIST)/Paths_MicroHs.hs
	@mkdir -p $(MCABALBIN)
	@mkdir -p $(MDIST)
	bin/mhs -z $(MHSINCNP) -i$(MDIST) $(MAINMODULE) -o$(MCABALBIN)/mhs
	@mkdir -p $(MRUNTIME)
	cp targets.conf $(MDATA)
	cp src/runtime/*.[ch] $(MRUNTIME)

$(MDIST)/Paths_MicroHs.hs:
	@mkdir -p $(MDIST)
	@echo 'module Paths_MicroHs where { import qualified Prelude(); import MHSPrelude; import Data.Version; version :: Version; version = makeVersion [$(HVERSION)]; getDataDir :: IO FilePath; getDataDir = return "$(MDATA)" }' > $(MDIST)/Paths_MicroHs.hs

$(MCABALBIN)/cpphs: bin/cpphs
	@mkdir -p $(MCABALBIN)
	cp bin/cpphs $(MCABALBIN)

$(MCABALBIN)/mcabal: bin/mcabal
	@mkdir -p $(MCABALBIN)
	cp bin/mcabal $(MCABALBIN)

$(MCABALMHS)/packages/$(BASE).pkg: bin/mhs lib/*.hs lib/*/*.hs lib/*/*/*.hs
	bin/mhs -P$(BASE) -o$(BASE).pkg -ilib $(BASEMODULES)
	bin/mhs -Q $(BASE).pkg $(MCABALMHS)
	@rm $(BASE).pkg

#install: $(MCABALBIN)/mhs $(MCABALBIN)/cpphs $(MCABALBIN)/mcabal $(MCABALMHS)/packages/$(BASE).pkg
#	@echo $$PATH | tr ':' '\012' | grep -q $(MCABALBIN) || echo '***' Add $(MCABALBIN) to the PATH

# mkdir ~/.mcabal/packages/array-0.5.6.0

preparedist:	newmhsz bootstrapcpphs
	rm -f generated/mcabal.c
	make generated/mcabal.c

install:	installmsg minstall

installmsg:
	@echo '***************************************************'
	@echo "* Installing MicroHs $(VERSION)"
	@echo "*  Binaries (in $(MCABALBIN)):"
	@echo '*    mhs     - MicroHs compiler'
	@echo '*    cpphs   - C preprocessor'
	@echo '*    mcabal  - cabal for MicroHs'
	@echo '*  Libraries:'
	@echo '*    base (bytestring, directory, filepath, text)'
	@echo '***************************************************'
	@echo ''

minstall:	bin/cpphs bin/mcabal $(MCABALBIN)/mhs
	cp bin/cpphs bin/mcabal $(MCABALBIN)
	cd lib; PATH=$(MCABALBIN):"$$PATH" mcabal $(MCABALGMP) install
# We don't really need to rebuild mhs
#	PATH=$(MCABALBIN):"$$PATH" mcabal install
	@echo $$PATH | tr ':' '\012' | grep -q $(MCABALBIN) || echo '***' Add $(MCABALBIN) to the PATH

#####
# Hugs
HUGS= runhugs
HUGSINCS= '+Phugs:src:paths:{Hugs}/packages/*:hugs/obj' -98 +o +w -h100m

generated/hmhs.c:
	@mkdir -p generated
	$(HUGS) $(HUGSINCS) hugs/Main.hs $(MHSINC) $(MAINMODULE) -ogenerated/hmhs.c

bin/hmhs: generated/hmhs.c
	@mkdir -p bin
	$(CCEVAL) generated/hmhs.c -o bin/hmhs
