## Results of the research.

CEK is a fine first step, but this machine is unoptimized. Eventually we'll need something better. Perhaps something along the lines of eval/apply. It is particularly nice how GHC has a special-purpose language for evaluation (the one that gets executed by the STG machine).

Some minimalistic machines are implemented [here](https://gist.github.com/effectfully/f742e2f846e03a2e2fd62765b642d515).

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
Clear definitions of CK, CEK (except this one contains a very unfortunate typo in the `appR-λ` case, see the K machine from "call-by-name, call-by-value and abstract machines (2012)" for the correct version of this clause), CESK, etc machines. That CESK machine relies on garbage collection in order to clean up redundant substitutions (the problem with the CEK machine described above). I wonder whether it would make sense to just know which variables are where used in the style of [Everybody's Got To Be Somewhere](https://github.com/pigworker/EGTBS/blob/master/EGTBS.pdf) or something, so we can deterministically prune environments.

## [Implementing functional languages with abstract machines (2015), Hayo Thielecke](https://www.cs.bham.ac.uk/~hxt/2015/compilers/compiling-functional.pdf)
A historical overview and a very clear implementation of the CEK machine that differs from the common one (or maybe this is the common one, I don't know, it just differs). Has a very elaborted example. Do not see whether this implementation is better, worse or what.

## [Distilling Abstract Machines (2014), Accattoli et al](https://lipn.univ-paris13.fr/~mazza/papers/DistillingAbstractMachines-ICFP2014.pdf)
Formal analysis of various machines. Invariants that for each machine hold are explicitly specified. Doesn't seem terribly useful for us.

## [Simplification of Abstract Machine for Functional Language and Its Theoretical Investigation](http://www.jsoftware.us/vol10/97-CA010.pdf)
Improved SECD machine. Importance is unclear.

## [Compiling With CPS](https://jozefg.bitbucket.io/posts/2015-04-30-cps.html)
Seems like something that should be studied. This applies to the topic in general.

## [From Krivine’s machine to the Caml implementations (Xavier Leroy)](https://xavierleroy.org/talks/zam-kazam05.pdf)
This is a must read.

> An illustration of the strengths and limitations of abstract machines for the purpose of efficient execution of strict functional language.

Makes some strong claims (refers to GHC and the standard OCaml compiler):

> In every area where abstract machines help, there are arguably better alternatives

> Abstract machines do many things well but none very well.

> # On the usefulness of abstract machines

> As a discovery tool: many of the key issues (e.g. eval-apply vs. push-enter) were discovered by thinking in terms of abstract machines, even though they are also apparent in terms of translations to lower-level functional languages.

> As a tool to prove compiler correctness: both theoretician’s abstract machines and practitioner’s abstract machines can be proved correct w.r.t. the λ-calculus (using e.g. explicit substitutions), or derived in a systematic, semantics-preserving way.

> As a cheap implementation device: bytecode interpreters offer 1 / 4 of the performance of optimizing native-code compilers, at 1 / 20 of the implementation cost.

A lot of this is about the OCaml bytecode interpreter (ZAM/ZAM2), so
it's probably worth having a look at the 
[Zinc Report](https://xavierleroy.org/bibrefs/Leroy-ZINC.html), Leroy's
description of his initial implementation of the OCaml system.  It's
from 1990, but still quite relevant. In particular there's a
description of the architecture of the bytecode interpreter, which is highly efficient (partly because it's implemented in C); I don't think
the design's changed too much in the interim.

## [B. Accattoli, B. Barras. Environments and the Complexity of Abstract Machines, 2017](https://sites.google.com/site/beniaminoaccattoli/Accattoli%2C%20Barras%20-%20Environments%20and%20the%20Complexity%20of%20Abstract%20Machines.pdf?attredirects=0)
Analyses efficiency of various machines. Call-by-name and call-by-need, but the paper claims that results also apply to call-by-value.

----

## Machines for lazy evaluation
Here are some papers dealing with machines which evaluate &lambda;-terms using call-by-name/lazy strategies.

[Jean-Louis Krivine: A call-by-name lambda-calculus machine](https://www.irif.fr/~krivine/articles/lazymach.pdf).
Krivine's machine was one of the first machines for call-by-name evaluation and 
has had a great deal of influence on subsequent research.  It was designed in the 1980s
but not published until 2007 (see below). The machine is simple but inefficient 
because it is not lazy: if a term is used more than once then it will have to be 
evaluated more than once.

[Peter Sestoft: Deriving a Lazy Abstract Machine](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.50.4314).
This starts by considering a [machine due to Launchbury](https://www.researchgate.net/publication/2639371_A_Natural_Semantics_for_Lazy_Evaluation)
which is essentially a lazy version of the Krivine machine.  Sestoft gradually improves the
machine by adding new features to the calculus and corresponding features to the machine.
This is a very revealing paper because it gives a principled derivation of the machine, clearly showing
the reasons for various features of the final machine.

[Daniel P. Friedman, Abdulaziz Ghuloum, Jeremy G. Siek, Onnie Lynn Winebarger: Improving the Lazy Krivine Machine](ftp://www.cs.indiana.edu/pub/techreports/TR581.pdf) .
This paper introduces further improvements to Sestoft's machine (see above). The underlying
calculus remains simple (and similar to Plutus Core), so this paper is perhaps more relevant 
from our point of view.  The paper can be found at ftp://www.cs.indiana.edu/pub/techreports/TR581.pdf .

[Rémi Douence,  Pascal Fradet:  The Next 700 Krivine Machines](https://hal.inria.fr/inria-00000940).
This studies a number of other variants of the Krivine machine and gives a good idea of the
(very large) space of possibilities for abstract machine implementation.

With the exception of the paper by Sestoft, all of the above papers can be found in
a [special issue of Higher-Order and Symbolic Computation](https://dl.acm.org/citation.cfm?id=1325146&picked=prox) 
which contains other papers that may be worth looking at.
<!---HOSC,  Volume 20 Issue 3, September 2007 --->

----

All of the papers above consider machines based on the Krivine Machine; however there are at least two
other approaches to lazy evaluation which have inspired a lot of research: 
*  Supercombinator-based machines such as the [Three Instruction Machine (TIM)](https://pdfs.semanticscholar.org/a19d/894a2290e2eddca59dd0598c00c5c7dd6793.pdf) of Fairbairn and Wray.
* Graph reduction machines, including the well-known [STG machine](https://www.microsoft.com/en-us/research/wp.../04/spineless-tagless-gmachine.pdf).

We haven't looked into the literature carefully here because neither of these types of machine
deals directly with &lambda;-calculus: a preliminary translation step would be required, which 
would complicate things for us. Also, graph reduction is not so easy to implement.

----

## Olivier Danvy's work

[Olivier Danvy](https://www.yale-nus.edu.sg/about/faculty/olivier-danvy/) 
and his collaborators have done some very interesting work on abstract machines.  In particular,
he has a technique for automatically deriving abstract machines from
evaluators (essentially the CPS transformation followed by defunctionalisation),and he's able to use this to obtain things like the SECD and CEK machines in a 
principled way, rather than just producing them out of thin air.  I don't know if this is directly relevant to what we're doing, but it's 
very instructive.  

See Chapter 3 of 
[Danvy's habilitation thesis](http://www.brics.dk/~danvy/DSc/00_dissertation.pdf)
and the following reports in particular:

* [A Functional Correspondence between Evaluators and Abstract Machines](http://www.brics.dk/RS/03/13/index.html)
* [From Interpreter to Compiler and Virtual Machine: A Functional Derivation](http://www.brics.dk/RS/03/14/index.html)
* [A Rational Deconstruction of Landin’s SECD Machine](http://www.brics.dk/RS/03/33/)

For lazy and effectful machines see

* [A Functional Correspondence between Call-by-Need Evaluators and Lazy Abstract Machines](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.59.7417)
* [A functional correspondence between monadic evaluators and abstract machines for languages with computational effects](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.100.4883)