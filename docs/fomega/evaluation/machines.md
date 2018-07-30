## [Understanding Plotkin's Call-By-Name, Call-By-Value and the λ-Calculus (2016)](http://languagengine.co/blog/plotkin-cbn-cbv/)
The CK machine with two states similar to the one from the Plutus Core specification (this is no coincidence).

## [call-by-name, call-by-value and abstract machines (2012), Remy Viehof](https://www.ru.nl/publish/pages/769526/cbn_cbv_and_ams_remyviehoff.pdf)
Clear implementation of the K machine (with environments, so, I suppose, it should be called the EK machine).

## [From Operational Semantics to Abstract Machinesl (1992), John Hannan, Dale Miller](http://www.lix.polytechnique.fr/~dale/papers/mscs92.pdf)
Implementations of the Krivine and the SECD machines.

## [Programming Languages and Lambda Calculi (2006), Matthias Felleisen, Matthew Flatt](http://ecee.colorado.edu/ecen5533/fall11/reading/pllc.pdf)
Comprehensive descriptions of various machines including the CK and CEK ones, but somewhat hard to read. Also describes what the problems with the CEK machine are. Namely, unused subsitutions consume large amount of space. Other machines of no apparent relevance are considered.

## [Abstract machines for programming language implementation (1999), Stephan Diehla, Pieter Hartel, Peter Sestoft](http://www.inf.ed.ac.uk/teaching/courses/lsi/diehl_abstract_machines.pdf)
Extensive and shallow overview of abstract machines.

## [AUTOMATING ABSTRACT INTERPRETATION OF ABSTRACT MACHINES (2015), James Ian Johnson](https://arxiv.org/pdf/1504.08033.pdf)
Clear definitions of CK, CEK (except this one contains a very unfortunate typo in the `appR-λ` case, see the K machine from "call-by-name, call-by-value and abstract machines (2012)" for the correct version), CESK, etc machines. That CESK machine relies on garbage collection in order to clean up redundant substitutions (the problem with the CEK machine described above). I wonder whether it would make sense to just know which variables are where used in the style of [Everybody's Got To Be Somewhere](https://github.com/pigworker/EGTBS/blob/master/EGTBS.pdf) or something, so we can deterministically prune environments.

## [Implementing functional languages with abstract machines (2015), Hayo Thielecke](https://www.cs.bham.ac.uk/~hxt/2015/compilers/compiling-functional.pdf)
A historical overview and a very clear implementation of the CEK machine that differs from the common one (or maybe this is the common one, I don't know, it just differs). Has a very elaborted example. Do not see whether this implementation is better, worse or what.

## https://lipn.univ-paris13.fr/~mazza/papers/DistillingAbstractMachines-ICFP2014.pdf

## [Simplification of Abstract Machine for Functional Language and Its Theoretical Investigation](http://www.jsoftware.us/vol10/97-CA010.pdf)
Improved SECD machine. Importance is unclear.

## [Compiling With CPS](https://jozefg.bitbucket.io/posts/2015-04-30-cps.html)
Seems like something that should be studied. This applies to the topic in general.

## Personal investigations
[minimal implementations of various machines](https://gist.github.com/effectfully/f742e2f846e03a2e2fd62765b642d515#file-a-minimalistic-ck-machine-agda).

