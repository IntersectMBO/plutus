MHS=../bin/gmhs
TMHS=$(MHS) -i../lib
EVAL=../bin/mhseval +RTS -H1M -RTS
.PHONY: test nfib clean errtest alltest cache info

alltest:	info test errtest
# interactivetest

cache:
	rm -f .mhscache
	$(TMHS) -CW AllOfLib

info:
	$(TMHS) Info       && $(EVAL)

test:
	$(TMHS) Hello      && $(EVAL) > Hello.out      && diff Hello.ref Hello.out
#	$(TMHS) IOTest     && (echo q | $(EVAL) a bb ccc | sed 's/^[0-9]*ms/1ms/' > IOTest.out) && diff IOTest.ref IOTest.out
	$(TMHS) Serdes     && $(EVAL) > Serdes.out     && diff Serdes.ref Serdes.out
	$(TMHS) StringTest && $(EVAL) > StringTest.out && diff StringTest.ref StringTest.out
	$(TMHS) ListTest   && $(EVAL) > ListTest.out   && diff ListTest.ref ListTest.out
	$(TMHS) Fac        && $(EVAL) > Fac.out        && diff Fac.ref Fac.out
	$(TMHS) Misc       && $(EVAL) > Misc.out       && diff Misc.ref Misc.out
	$(TMHS) Case       && $(EVAL) > Case.out       && diff Case.ref Case.out
	$(TMHS) Arith      && $(EVAL) > Arith.out      && diff Arith.ref Arith.out
	$(TMHS) Guard      && $(EVAL) > Guard.out      && diff Guard.ref Guard.out
	$(TMHS) Newtype    && $(EVAL) > Newtype.out    && diff Newtype.ref Newtype.out
	$(TMHS) LitMatch   && $(EVAL) > LitMatch.out   && diff LitMatch.ref LitMatch.out
	$(TMHS) Word       && $(EVAL) > Word.out       && diff Word.ref Word.out
	$(TMHS) Integer    && $(EVAL) > Integer.out    && diff Integer.ref Integer.out
	$(TMHS) Enum       && $(EVAL) > Enum.out       && diff Enum.ref Enum.out
	$(TMHS) MutRec     && $(EVAL) > MutRec.out     && diff MutRec.ref MutRec.out
	$(TMHS) LocalPoly  && $(EVAL) > LocalPoly.out  && diff LocalPoly.ref LocalPoly.out
	$(TMHS) Rank2      && $(EVAL) > Rank2.out      && diff Rank2.ref Rank2.out
	$(TMHS) Catch      && $(EVAL) > Catch.out      && diff Catch.ref Catch.out
	$(TMHS) FArith     && $(EVAL) > FArith.out     && diff FArith.ref FArith.out
	$(TMHS) Infix      && $(EVAL) > Infix.out      && diff Infix.ref Infix.out
	$(TMHS) Class      && $(EVAL) > Class.out      && diff Class.ref Class.out
	$(TMHS) Eq         && $(EVAL) > Eq.out         && diff Eq.ref Eq.out
	$(TMHS) Floating   && $(EVAL) > Floating.out   && diff Floating.ref Floating.out
	$(TMHS) Default    && $(EVAL) > Default.out    && diff Default.ref Default.out
	$(TMHS) Multi      && $(EVAL) > Multi.out      && diff Multi.ref Multi.out
	$(TMHS) Exists     && $(EVAL) > Exists.out     && diff Exists.ref Exists.out
	$(TMHS) TypeEq     && $(EVAL) > TypeEq.out     && diff TypeEq.ref TypeEq.out
	$(TMHS) Sieve      && $(EVAL) > Sieve.out      && diff Sieve.ref Sieve.out
	$(TMHS) Dict       && $(EVAL) > Dict.out       && diff Dict.ref Dict.out
	$(TMHS) Symbol     && $(EVAL) > Symbol.out     && diff Symbol.ref Symbol.out
	$(TMHS) FunDep     && $(EVAL) > FunDep.out     && diff FunDep.ref FunDep.out
	$(TMHS) TypeLits   && $(EVAL) > TypeLits.out   && diff TypeLits.ref TypeLits.out
	$(TMHS) View       && $(EVAL) > View.out       && diff View.ref View.out
	$(TMHS) IOArray    && $(EVAL) > IOArray.out    && diff IOArray.ref IOArray.out
	$(TMHS) ST         && $(EVAL) > ST.out         && diff ST.ref ST.out
	$(TMHS) HigherKind && $(EVAL) > HigherKind.out && diff HigherKind.ref HigherKind.out
	$(TMHS) PolyKind   && $(EVAL) > PolyKind.out   && diff PolyKind.ref PolyKind.out
	$(TMHS) Record     && $(EVAL) > Record.out     && diff Record.ref Record.out
	$(TMHS) Deriving   && $(EVAL) > Deriving.out   && diff Deriving.ref Deriving.out
	$(TMHS) Unicode    && $(EVAL) > Unicode.out    && diff Unicode.ref Unicode.out
	$(TMHS) BindPat    && $(EVAL) > BindPat.out    && diff BindPat.ref BindPat.out
	$(TMHS) Read       && $(EVAL) > Read.out       && diff Read.ref Read.out
	$(TMHS) ListCompr  && $(EVAL) > ListCompr.out  && diff ListCompr.ref ListCompr.out
	$(TMHS) ParseInd   && $(EVAL) > ParseInd.out   && diff ParseInd.ref ParseInd.out
	$(TMHS) Infer      && $(EVAL) > Infer.out      && diff Infer.ref Infer.out
	$(TMHS) Enum       && $(EVAL) > Enum.out       && diff Enum.ref Enum.out
	$(TMHS) RecMdl     && $(EVAL) > RecMdl.out     && diff RecMdl.ref RecMdl.out
	$(TMHS) ForeignPtr && $(EVAL) > ForeignPtr.out && diff ForeignPtr.ref ForeignPtr.out
	$(TMHS) Array      && $(EVAL) > Array.out      && diff Array.ref Array.out
	$(TMHS) Eq1        && $(EVAL) > Eq1.out        && diff Eq1.ref Eq1.out
	$(TMHS) Irref      && $(EVAL) > Irref.out      && diff Irref.ref Irref.out
	$(TMHS) DfltSig    && $(EVAL) > DfltSig.out    && diff DfltSig.ref DfltSig.out
	$(TMHS) Bytestring && $(EVAL) > Bytestring.out && diff Bytestring.ref Bytestring.out
	$(TMHS) Text       && $(EVAL) > Text.out       && diff Text.ref Text.out
	$(TMHS) ImpMet     && $(EVAL) > ImpMet.out     && diff ImpMet.ref ImpMet.out
	$(TMHS) MultiIf    && $(EVAL) > MultiIf.out    && diff MultiIf.ref MultiIf.out
	$(TMHS) LameCase   && $(EVAL) > LameCase.out   && diff LameCase.ref LameCase.out
	$(TMHS) NoForall   && $(EVAL) > NoForall.out   && diff NoForall.ref NoForall.out
	$(TMHS) Bang       && $(EVAL) > Bang.out       && diff Bang.ref Bang.out
	$(TMHS) MString    && $(EVAL) > MString.out    && diff MString.ref MString.out
	$(TMHS) OrPat      && $(EVAL) > OrPat.out      && diff OrPat.ref OrPat.out
	$(TMHS) PartRed    && $(EVAL) > PartRed.out    && diff PartRed.ref PartRed.out
	$(TMHS) PatSyn     && $(EVAL) > PatSyn.out     && diff PatSyn.ref PatSyn.out
	$(TMHS) Coerce     && $(EVAL) > Coerce.out     && diff Coerce.ref Coerce.out
	$(TMHS) PatBind    && $(EVAL) > PatBind.out    && diff PatBind.ref PatBind.out
	$(TMHS) EmptyCase  && $(EVAL)
	$(TMHS) NumUnder   && $(EVAL) > NumUnder.out   && diff NumUnder.ref NumUnder.out
	$(TMHS) LocalFix   && $(EVAL) > LocalFix.out   && diff LocalFix.ref LocalFix.out
	$(TMHS) TypeApp    && $(EVAL) > TypeApp.out    && diff TypeApp.ref TypeApp.out
	$(TMHS) Do         && $(EVAL) > Do.out         && diff Do.ref Do.out
	$(TMHS) Via        && $(EVAL) > Via.out        && diff Via.ref Via.out
	$(TMHS) ByteStringIO && $(EVAL) > ByteStringIO.out && diff ByteStringIO.ref ByteStringIO.out
	$(TMHS) BitCount   && $(EVAL) > BitCount.out   && diff BitCount.ref BitCount.out
	$(TMHS) Bounded    && $(EVAL) > Bounded.out    && diff Bounded.ref Bounded.out
	$(TMHS) Typeable   && $(EVAL) > Typeable.out   && diff Typeable.ref Typeable.out
	$(TMHS) Storable   && $(EVAL) > Storable.out   && diff Storable.ref Storable.out
	$(TMHS) StandDer   && $(EVAL) > StandDer.out   && diff StandDer.ref StandDer.out
	MHSCPPHS=../bin/cpphs \
	$(TMHS) Cpp        && $(EVAL) > Cpp.out        && diff Cpp.ref Cpp.out
	$(TMHS) Lit        && $(EVAL) > Lit.out        && diff Lit.ref Lit.out
	$(TMHS) TypeOp     && $(EVAL) > TypeOp.out     && diff TypeOp.ref TypeOp.out
	$(TMHS) Forall     && $(EVAL) > Forall.out     && diff Forall.ref Forall.out
	$(TMHS) Block      && $(EVAL) > Block.out      && diff Block.ref Block.out
	$(TMHS) Fork       && $(EVAL) > Fork.out       && diff Fork.ref Fork.out
	$(TMHS) Concur     && $(EVAL) > Concur.out     && diff Concur.ref Concur.out
	$(TMHS) MVar       && $(EVAL) > MVar.out       && diff MVar.ref MVar.out
	$(TMHS) Delay      && $(EVAL) > Delay.out      && diff Delay.ref Delay.out
	$(TMHS) ThrSt      && $(EVAL) > ThrSt.out      && diff ThrSt.ref ThrSt.out
	$(TMHS) Throw      && $(EVAL) > Throw.out      && diff Throw.ref Throw.out
	$(TMHS) RtsExn     && $(EVAL) > RtsExn.out     && diff RtsExn.ref RtsExn.out
	$(TMHS) Mask       && $(EVAL) > Mask.out       && diff Mask.ref Mask.out

# BROKEN: cannot compile binaries here
testforeign:
	MHSDIR=.. $(TMHS) ForeignC -of.exe && ./f.exe > ForeignC.out  && diff ForeignC.ref ForeignC.out

errtest:
	sh errtester.sh $(MHS) < errmsg.test

interactivetest:
	$(TMHS) < itest.in | sed -e '1,/^>/d' > itest.out && diff itest.ref itest.out

nfib:
	$(TMHS) Nfib && $(EVAL)

clean:
	rm -f *.out *.tmp *.js *.exe
