\documentclass{llncs}
\usepackage{hyperref}
\bibliographystyle{splncs04}
%\usepackage{ucs}
\usepackage[utf8]{inputenc}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{txfonts}
%\usepackage{bbm}
%\usepackage[greek,english]{babel}

% agda.sty wants to use the deprecated utf8x option, which
% many publishers don't like. So we do it ourselves

\usepackage{agda}

\usepackage{proof}

% this stuff is related to the Agda latex backend with inputenc/utf8
% not having heard of many characters...

\usepackage{newunicodechar}
\newunicodechar{∋}{$\ni$}
\newunicodechar{·}{$\cdot$}
\newunicodechar{⊢}{$\vdash$}
\newunicodechar{⋆}{${}^\star$}
\newunicodechar{Π}{$\Pi$}
\newunicodechar{⇒}{$\Rightarrow$}
\newunicodechar{ƛ}{$\lambdabar$}
\newunicodechar{∅}{$\emptyset$}
\newunicodechar{∀}{$\forall$}
\newunicodechar{ϕ}{$\Phi$}
\newunicodechar{ψ}{$\Psi$}
\newunicodechar{ρ}{$\rho$}
\newunicodechar{α}{$\alpha$}
\newunicodechar{β}{$\beta$}
\newunicodechar{μ}{$\mu$}
\newunicodechar{σ}{$\sigma$}
\newunicodechar{≡}{$\equiv$}
\newunicodechar{Γ}{$\Gamma$}
\newunicodechar{∥}{$\parallel$}
\newunicodechar{Λ}{$\Lambda$}
\newunicodechar{₂}{$~_2$}
\newunicodechar{θ}{$\theta$}
\newunicodechar{Θ}{$\Theta$}
\newunicodechar{∘}{$\circ$}
\newunicodechar{Δ}{$\Delta$}
\newunicodechar{λ}{$\lambda$}
\newunicodechar{⊧}{$\models$}
\newunicodechar{⊎}{$\uplus$}
\newunicodechar{η}{$\eta$}
\newunicodechar{⊥}{$\bot$}
\newunicodechar{Σ}{$\Sigma$}
\newunicodechar{ξ}{$\xi$}
\newunicodechar{₁}{$1$}
\newunicodechar{ℕ}{$\mathbb{N}$}
\newunicodechar{ᶜ}{${}^c$}
\newunicodechar{Φ}{$\Phi$}
\newunicodechar{Ψ}{$\Psi$}
\newunicodechar{⊤}{$\top$}

\newunicodechar{→}{$\rightarrow$}
\newunicodechar{×}{$\times$}


\usepackage{hyperref}
\usepackage{cleveref}

\author{James Chapman\inst{1}\orcidID{0000-0001-9036-8252}
  \and Roman Kireev\inst{1}\orcidID{0000-0003-4687-2739}
  \and Chad Nester\inst{2}
  \and Philip Wadler\inst{2}\orcidID{0000-0001-7619-6378}}
  \institute{IOHK, Hong Kong
\email{\{james.chapman,roman.kireev\}@iohk.io}
\and
University of Edinburgh, UK
\email{\{cnester,wadler\}@inf.ed.ac.uk}}
\title{System~$F$ in Agda, for fun and profit}

\begin{document}
\maketitle

\begin{abstract}

System~$F$, also known as the polymorphic λ-calculus, is a typed
λ-calculus independently discovered by the logician Jean-Yves Girard
and the computer scientist John Reynolds. We consider $F_{\omega\mu}$,
which adds higher-order kinds and iso-recursive types. We present the
first complete, intrinsically typed, executable, formalisation of
System~$F_{\omega\mu}$ that we are aware of. The work is motivated by
verifying the core language of a smart contract system based on
System~$F_{\omega\mu}$. The paper is a literate Agda script
\cite{formalisation}.

\end{abstract}


\section{Introduction}

System~$F$, also known as the polymorphic $\lambda$-calculus, is a
typed $\lambda$-calculus independently discovered by the logician
Jean-Yves Girard and the computer scientist John Reynolds.  System~$F$
extends the simply-typed $\lambda$-calculus (STLC).  Under the
principle of Propositions as Types, the $\to$ type of STLC corresponds
to implication; to this System~F adds a $\forall$ type that
corresponds to universal quantification over propositions.
Formalisation of System~$F$ is tricky: it, when extended with
subtyping, formed the basis for the POPLmark challenge
\cite{POPLmark}, a set of formalisation problems widely attempted as a
basis for comparing different systems.

System~$F$ is small but powerful.  By a standard technique known as
Church encoding, it can represent a wide variety of datatypes,
including natural numbers, lists, and trees.  However, while
System~$F$ can encode the type ``list of $A$'' for any type $A$ that
can also be encoded, it cannot encode ``list'' as a function from
types to types.  For that one requires System~$F$ with higher-kinded
types, known as System~$F_\omega$.  Girard's original work also
considered this variant, though Reynolds did not.

The basic idea of System~$F_\omega$ is simple.  Not only does each
\emph{term} have a \emph{type}, but also each \emph{type} level object
has a \emph{kind}. Notably, type \emph{families} are classified by
higher kinds.  The first level, relating terms and types, includes an
embedding of STLC (plus quantification); while the second level,
relating types and kinds, is an isomorphic image of STLC.

Church encodings can represent any algebraic datatype recursive only in
positive positions; though extracting a component of a structure, such
as finding the tail of a list, takes time proportional to the size of
the structure.  Another standard technique, known as Scott encoding,
can represent any algebraic type whatsoever; and extracting a
component now takes constant time.  However, Scott encoding requires
a second extension to System~$F$, to represent arbitrary recursive
types, known as System~$F_\mu$.  The system with both extensions
is known as System~$F_{\omega\mu}$, and will be the subject of our
formalisation.

Terms in Systems~$F$ and $F_\omega$ are strongly normalising.
Recursive types with recursion in a negative position permit encoding
arbitrary recursive functions, so normalisation of terms in
Systems~$F_\mu$ and $F_{\omega\mu}$ may not terminate.  However,
constructs at the type level of Systems~$F_\omega$ and $F_{\omega\mu}$
are also strongly normalising.

There are two approaches to recursive types, \emph{equi-recursive} and
\emph{iso-recursive} \cite{pierce:tapl}.  In an equi-recursive
formulation, the types $\mu \alpha. A[\alpha]$ and $A[\mu
\alpha. A[\alpha]]$ are considered equal, while in an iso-recursive
formulation they are considered isomorphic, with an \emph{unfold} term
to convert the former to the latter, and a \emph{fold} term to convert
the other way.  Equi-recursive formulation makes coding easier, as it
doesn't require extra term forms.  But it makes type checking more
difficult, and it is not known whether equi-recursive types for
System~$F_{\omega\mu}$ are decidable
\cite{dreyer:recursive-modules,cai.giarrusso.ostermann}. Accordingly,
we use iso-recursive types, which are also used by Dreyer
\cite{dreyer:thesis} and Brown and Palsberg \cite{brown.palsberg}.

There are also two approaches to formalising a typed calculus,
\emph{extrinsic} and \emph{intrinsic}
\cite{reynolds:intrinsic-extrinsic}.  In an extrinsic formulation,
terms come first and are assigned types later, while in an intrinsic
formulation, types come first and a term can be formed only at a given
type.  The two approaches are sometimes associated with Curry and
Church, respectively \cite{hindley.seldin}.  There is also the
dichotomy between named variables and de Bruijn indices.  De Bruijn
indices ease formalisation, but require error-prone arithmetic to move
a term underneath a lambda expression.  An intrinsic formulation
catches such errors, because they would lead to incorrect types.
Accordingly, we use an intrinsic formulation with de Bruijn indices.
The approach we follow was introduced by Altenkirch and Reus
\cite{altenkirch.reus:welltyped}, and used by Chapman
\cite{chapman:thesis} and Allais et
al. \cite{allais.chapman.mcbride.mckinna} among others.

\subsection{For Fun and Profit}

Our interest in System~$F_{\omega\mu}$ is far from merely theoretical.
Input Output HK Ltd. (IOHK) is developing the Cardano blockchain,
which features a smart contract language known as Plutus
\cite{platform}.  The part of the contract that runs off-chain is
written in Haskell with an appropriate library, while the part of the
contract that runs on-chain is written using Template Haskell and
compiled to a language called Plutus Core.  Any change to the core
language would require all participants of the blockchain to update their
software, an event referred to as a \emph{hard fork}.  Hard forks are
best avoided, so the goal with Plutus Core was to make it so simple
that it is unlikely to need revision.  The design settled on is
System~$F_{\omega\mu}$ with suitable primitives, using Scott encoding
to represent data structures.  Supported primitives include integers,
bytestrings, and a few cryptographic and blockchain-specific
operations.

The blockchain community puts a high premium on rigorous specification
of smart contract languages.  Simplicity, a proposed smart contract
language for Bitcoin, has been formalised in Coq
\cite{simplicity}. The smart contract language Michelson, used by
Tezos, has also been formalised in Coq \cite{michelson-coq}. EVM, the
virtual machine of Ethereum, has been formalised in K \cite{kevm}, in
Isabelle/HOL \cite{hirai,amani.begel.bortin.staples}, and in $F^*$
\cite{grishchenko.maffei.schneidewind}. For a more complete account
of blockchain projects involving formal methods see
\cite{verification-survey}.

IOHK funded the development of our formalisation of
System~$F_{\omega\mu}$ because of the correspondence to Plutus Core.
The formal model in Agda and associated proofs give us high assurance
that our specification is correct. Further, we plan to use the
evaluator that falls out from our proof of progress for testing
against the evaluator for Plutus Core that is used in Cardano.

\subsection{Contributions}

This paper represents the first complete intrinsically typed,
executable, formalisation of System~$F_{\omega\mu}$ that we are aware
of. There are other intrinsically typed formalisations of fragments of
System $F_{\omega\mu}$. But, as far as we are aware none are
complete. András Kovács has formalised System $F_\omega$\cite{kovacs}
using hereditary substitutions \cite{watkins} at the type
level. Kovács' formalisation does not cover iso-recursive types and
also does not have the two different presentations of the syntax and
the metatheory relating them that are present here.

Intrinsically typed formalisations of arguably more challenging
languages exist such as those of Chapman \cite{chapman:thesis} and
Danielsson \cite{danielsson} for dependently typed languages. However,
they are not complete and do not consider features such as recursive
types. This paper represents a more complete treatment of a different
point in the design space which is interesting in its own right and
has computation at the type level but stops short of allowing
dependent types. We believe that that techniques described here will
be useful when scaling up to greater degrees of dependency.

A key challenge with the intrinsically typed approach for System
$F_\omega$ is that due to computation at the type level, it is
necessary to make use of the implementations of type level operations
and even proofs of their correctness properties when defining the term
level syntax and term level operations. Also, if we want to run term
level programs, rather than just formalise them, it is vital that
these proofs of type level operations compute, which means that we
cannot assume any properties or rely on axioms in the metatheory such
as functional extensionality. Achieving this level of completeness is
a contribution of this paper as is the fact that this formalisation is
executable. We do not need extensionality despite using higher order
representations of renamings, substitutions, and (the semantics of)
type functions. First order variants of these concepts are more
cumbersome and long winded to work with. As the type level language is
a strongly normalising extension of the simply-typed
$\lambda$-calculus we were able to leverage work about renaming,
substitution and normalisation from simply-typed
$\lambda$-calculus. Albeit with the greater emphasis that proofs must
compute. We learnt how to avoid using extensionality when reasoning
about higher order/functional representations of renamings and
substitutions from Conor McBride. The normalisation algorithm is
derived from work by Allais et al. and McBride
\cite{allias.mcbride.boutillier:neutral,mcbride:data}. The
normalisation proof also builds on their work, and in our opinion,
simplifies and improves it as the uniformity property in the
completeness proof becomes simply a type synonym required only at
function type (kind in our case) rather than needing to be mutually
defined with the logical relation at every type (kind), simplifying
the construction and the proofs considerably. In addition we work with
β-equality not βη-equality which, in the context of NBE makes things a
little more challenging. The reason for this choice is that our smart
contract core language Plutus Core has only β-equality.

Another challenge with the intrinsically typed approach for System
$F_\omega$, where typing derivations and syntax coincide, is that the
presence of the conversion rule in the syntax makes computation
problematic as it can block $\beta$-reduction. Solving/avoiding this
problem is a contribution of this paper.

The approach to the term level and the notation borrow heavily from
PLFA \cite{wadler.koke} where the chapters on STLC form essentially a
blueprint for and a very relevant introduction to this work. The idea
of deriving an evaluator from a proof of progress appears in PLFA, and
appears to be not widely known \cite{wadler:sbmf}.
 
\subsection{Overview}

This paper is a literate Agda program that is machine checked and
executable either via Agda's interpreter or compiled to Haskell. The
code (i.e. the source code of the paper) is available as a supporting
artefact. In addition the complete formalisation of the extended
system (Plutus Core) on which this paper is based is also available as
a supporting artefact.

In the paper we aim to show the highlights of the formalisation: we
show as much code as possible and the statements of significant lemmas
and theorems. We hide many proofs and minor auxiliary lemmas.

Dealing with the computation in types and the conversion rule was the
main challenge in this work for us. The approaches taken to variable
binding, renaming/substitution and normalisation lifted
relatively easily to this setting. In addition to the two versions of
syntax where types are (1) not normalised and (2) completely
normalised we also experimented with a version where types are in weak
head normal form (3). In (1) the conversion rule takes an inductive
witness of type equality relation as an argument. In (2) conversion is
derivable as type equality is replaced by identity. In (3), the type
equality relation in conversion can be replaced by a witness of a logical
relation that computes, indeed it is the same logical relation as
described in the completeness of type normalisation proof. We did not
pursue this further in this work so far as this approach is not
used in Plutus Core but this is something that we would like to
investigate further in future.

In \cref{sec:intrinsically-typed} we introduce intrinsically typed
syntax (kinds, types and terms) and the dynamics of types (type
equality). We also introduce the necessary syntactic operations for
these definitions: type weakening and substitution (and their
correctness properties) are necessary to define terms. In
\cref{sec:algorithmic} we introduce an alternative version of the
syntax where the types are $\beta$-normal forms. We also introduce the
type level normalisation algorithm, its correctness proof and a
normalising substitution operation on normal types. In
\cref{sec:correspondence} we reconcile the two versions of the syntax,
prove soundness and completeness results and also demonstrate that
normalising the types preserves the \emph{semantics} of terms where
semantics refers to corresponding untyped terms. In
\cref{sec:operational-semantics} we introduce the dynamics of the
algorithmic system (type preserving small-step reduction) and we prove
progress in \cref{sec:algorithmic}. Preservation holds
intrinsically. In \cref{sec:execution} we provide a step-indexed
evaluator that we can use to execute programs for a given number of
reduction steps. In \cref{sec:examples} we show examples of Church and
Scott Numerals. In \cref{sec:real-world} we discuss extensions of the
formalisation to higher kinded recursive types and intrinsically sized
integers and bytestrings.

\section{Intrinsically typed syntax of System $F_{\omega\mu}$}
\label{sec:intrinsically-typed}

We take the view that when writing a program such as an interpreter we
want to specify very precisely how the program behaves on meaningful
input and we want to rule out meaningless input as early and as
conclusively as possible. Many of the operations we define in this
paper, including substitution, evaluation, and normalisation, are only
intended to work on well-typed input. In a programming language with a
less precise type system we might need to work under the informal
assumption that we will only ever feed meaningful inputs to our
programs and otherwise their behaviour is unspecified, and all bets
are off. Working in Agda we can guarantee that our programs will only
accept meaningful input by narrowing the definition of valid
input. This is the motivation for using intrinsic syntax as the
meaningful inputs are those that are guaranteed to be type correct and
in Agda we can build this property right into the definition of the
syntax.

In practice, in our setting, before receiving the input (some source
code in a file) it would have been run through a lexing, parsing,
scope checking and most importantly \emph{type checking} phase before
reaching our starting point in this paper: intrinsically typed
syntax. Formalising the type checker is future work.

One can say that in intrinsically typed syntax, terms carry their
types. But, we can go further, the terms are actually typing
derivations. Hence, the definition of the syntax and the type system,
as we present it, coincide: each syntactic constructor corresponds to
one typing rule and vice versa. As such we dispense with presenting
them separately and instead present them in one go.

There are three levels in this syntax:
\begin{enumerate}
\item kinds, which classify types;
\item types, which classify terms;
\item terms, the level of ordinary programs.
\end{enumerate}

\noindent The kind level is needed as there are functions at the type
level. Types appear in terms, but terms do not appear in types.

\subsection{Kinds}

The kinds consist of a base kind \AgdaInductiveConstructor{*}, which is
the kind of types, and a function kind.\footnote{The code in this paper
is typeset in \AgdaComment{colour}.}

\AgdaHide{
\begin{code}
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality
  using (subst; _≡_; refl; cong; cong₂; trans; sym)
open import Data.Sum as Sum renaming (inj₁ to inl; inj₂ to inr) 
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Fin

infix  4 _∋⋆_
infix  4 _⊢⋆_
infixl 5 _,⋆_

infix  6 Π
infixr 7 _⇒_

infix  5 ƛ
infixl 7 _·_
infix  9 S
\end{code}
}
\begin{code}
data Kind : Set where
  *    :  Kind                -- type
  _⇒_  :  Kind → Kind → Kind  -- function kind
\end{code}

Let \AgdaBound{K} and \AgdaBound{J} range over kinds.

\subsection{Type Contexts}

To manage the types of variables and their scopes we introduce
contexts. Our choice of how to deal with variables is already visible
in the representation of contexts. We will use de Bruijn indices to
represent variables. While this makes terms harder to write, it makes
the syntactic properties of the language clear and any potential
off-by-one errors etc. are mitigated by working with intrinsically
scoped terms and the fact that syntactic properties are proven
correct. We intend to use the language as a compilation target so ease
of manually writing programs in this language is not a high priority.

We refer to type contexts as \AgdaDatatype{Ctx${}^\star$} and reserve
the name \AgdaDatatype{Ctx} for term level contexts. Indeed, when a
concept occurs at both type and term level we often suffix the name of
the type level version with ${}^\star$.

Type contexts are essentially lists of types written in reverse. No
names are required.

\begin{code}
data Ctx⋆ : Set where
  ∅     :  Ctx⋆                -- empty context
  _,⋆_  :  Ctx⋆ → Kind → Ctx⋆  -- context extension
\end{code}

\noindent Let \AgdaBound{$\Phi$} and \AgdaBound{$\Psi$} range over
contexts.

\subsection{Type Variables}

We use de Bruijn indices for variables. They are natural numbers
augmented with additional kind and context information. The kind index
tells us the kind of the variable and the context index ensures that
the variable is in scope. It is impossible to write a variable that
isn't in the context. \AgdaInductiveConstructor{Z} refers to the last
variable introduced on the right hand end of the context. Adding one
to a variable via \AgdaInductiveConstructor{S} moves one position to
the left in the context. Note that there is no way to construct a
variable in the empty context as it would be out of scope. Indeed,
there is no way at all to construct a variable that is out of scope.

\begin{code}
data _∋⋆_ : Ctx⋆ → Kind → Set where
  Z : ∀ {ϕ J}              → ϕ ,⋆ J ∋⋆ J
  S : ∀ {ϕ J K}  → ϕ ∋⋆ J  → ϕ ,⋆ K ∋⋆ J
\end{code}

\noindent Let \AgdaBound{$\alpha$} and \AgdaBound{$\beta$} range over type
variables.

\subsection{Types}

Types, like type variables, are indexed by context and kind, ensuring
well-scopedness and well-kindedness. The first three constructors
\AgdaInductiveConstructor{`} \AgdaInductiveConstructor{$\lambdabar$}
and \AgdaInductiveConstructor{$\cdot$} are analogous to the terms of
STLC. This is extended with the \AgdaInductiveConstructor{$\Pi$} type
to classify type abstractions at the type level, function type
\AgdaInductiveConstructor{$\Rightarrow$} to classify functions, and
\AgdaInductiveConstructor{$\mu$} to classify recursive terms. Note
that \AgdaInductiveConstructor{$\Pi$},
\AgdaInductiveConstructor{$\Rightarrow$}, and
\AgdaInductiveConstructor{$\mu$} are effectively base types as they
live at kind \AgdaInductiveConstructor{*}.

\begin{code}
data _⊢⋆_ Φ : Kind → Set where
  `    :  ∀{J}     →  Φ ∋⋆ J                → Φ ⊢⋆ J      -- type variable
  ƛ    :  ∀{K J}   →  Φ ,⋆ K ⊢⋆ J           → Φ ⊢⋆ K ⇒ J  -- type lambda
  _·_  :  ∀{K J}   →  Φ ⊢⋆ K ⇒ J  → Φ ⊢⋆ K  → Φ ⊢⋆ J      -- type application
  _⇒_  :              Φ ⊢⋆ *      → Φ ⊢⋆ *  → Φ ⊢⋆ *      -- function type
  Π    :  ∀{K}     →  Φ ,⋆ K ⊢⋆ *           → Φ ⊢⋆ *      -- Pi/forall type
  μ    :              Φ ,⋆ * ⊢⋆ *           → Φ ⊢⋆ *      -- recursive type
\end{code}

\noindent Let \AgdaBound{A} and \AgdaBound{B} range over types.

\subsection{Type Renaming}

Types can contain functions and as such are subject to a nontrivial
equality relation. To explain the computation equation (the
$\beta$-rule) we need to define substitution for a single type
variable in a type. Later, when we define terms that are indexed by
their type we will need to be able to weaken types by an extra kind
(section \ref{sec:term-var}) and also, again, substitute for a
single type variable in a type (section \ref{sec:term}). There are
various different ways to define the required weakening and
substitution operations. We choose to define so-called parallel
renaming and substitution i.e. renaming/substitution of several
variables at once. Weakening and single variable substitution are
special cases of these operations.

We follow Altenkirch and Reus \cite{altenkirch.reus:welltyped} and
implement renaming first and then substitution using renaming. In our
opinion the biggest advantage of this approach is that it has a very
clear mathematical theory. The necessary correctness properties of
renaming are identified with the notion of a functor and the
correctness properties of substitution are identified with the notion
of a relative monad. For the purposes of reading this paper it is not
necessary to understand relative monads in detail. The important thing
is that, like ordinary monads, they have a return and bind and the
rules that govern them are the same. It is only the types of the
operations involved that are different. The interested reader may
consult \cite{relmon} for a detailed investigation of relative monads
and \cite{relmonformalized} for a directly applicable investigation of
substitution of STLC as a relative monad.

A type renaming is a function from type variables in one context to
type variables in another. This is much more flexibility than we
need. We only need the ability to introduce new variable on the right
hand side of the context. The simplicity of the definition makes it
easy to work with and we get some properties for free that we would
have to pay for with a first order representation, such as not needing
to define a lookup function, and we inherit the properties of functions
provided by $\eta$-equality, such as associativity of composition, for
free. Note that even though renamings are functions we do not require
our metatheory (Agda's type system) to support functional
extensionality. As pointed out to us by Conor McBride we only ever
need to make use of an equation between renamings on a point (a
variable) and therefore need only a pointwise version of equality on
functions to work with equality of renamings and substitutions.

\begin{code}
Ren⋆ : Ctx⋆ → Ctx⋆ → Set
Ren⋆ Φ ψ = ∀ {J} → Φ ∋⋆ J → ψ ∋⋆ J
\end{code}

\noindent
Let \AgdaBound{ρ} range over type renamings.

As we are going to push renamings through types we need to be able to
push them under a binder. To do this safely the newly bound variable
should remain untouched and other renamings should be shifted by one
to accommodate this. This is exactly what the
\AgdaFunction{lift⋆} function does and it is defined by
recursion on variables:

\begin{code}
lift⋆ : ∀ {ϕ ψ} → Ren⋆ ϕ ψ → ∀ {K} → Ren⋆ (ϕ ,⋆ K) (ψ ,⋆ K)
lift⋆ ρ Z      =  Z        -- leave newly bound variable untouched
lift⋆ ρ (S α)  =  S (ρ α)  -- apply renaming to other variables and add 1
\end{code}

\noindent
Next we define the action of renaming on types. This is defined
by recursion on the type. Observe that we lift the renaming when we
go under a binder and actually apply the renaming when we hit a
variable:

\begin{code}
ren⋆ : ∀ {ϕ ψ} → Ren⋆ ϕ ψ → ∀ {J} → ϕ ⊢⋆ J → ψ ⊢⋆ J
ren⋆ ρ (` α)       =  ` (ρ α)
ren⋆ ρ (ƛ B)       =  ƛ (ren⋆ (lift⋆ ρ) B)
ren⋆ ρ (A · B)     =  ren⋆ ρ A · ren⋆ ρ B
ren⋆ ρ (A ⇒ B)     =  ren⋆ ρ A ⇒ ren⋆ ρ B
ren⋆ ρ (Π B)       =  Π (ren⋆ (lift⋆ ρ) B)
ren⋆ ρ (μ B)       =  μ (ren⋆ (lift⋆ ρ) B)
\end{code}

\noindent Weakening is a special case of renaming. We apply the
renaming \AgdaInductiveConstructor{S} which does double duty as the
variable constructor, if we check the type of
\AgdaInductiveConstructor{S} we see that it is a renaming.

Weakening shifts all the existing variables one place to the left in
the context:

\begin{code}
weaken⋆ : ∀ {ϕ J K} → ϕ ⊢⋆ J → ϕ ,⋆ K ⊢⋆ J
weaken⋆ = ren⋆ S
\end{code}

\subsection{Type Substitution}
\label{sec:type-substitution}

Having defined renaming we are now ready to define substitution for
types. Substitutions are defined as functions from type variables to
types:

\begin{code}
Sub⋆ : Ctx⋆ → Ctx⋆ → Set
Sub⋆ ϕ ψ = ∀ {J} → ϕ ∋⋆ J → ψ ⊢⋆ J
\end{code}

\noindent
Let \AgdaBound{$\sigma$} range over substitutions.

We must be able to lift substitutions when we push them under
binders. Notice that we leave the newly bound variable intact and make
use of \AgdaFunction{weaken⋆} to weaken a term that is substituted.

\begin{code}
lifts⋆ : ∀ {ϕ ψ} → Sub⋆ ϕ ψ → ∀ {K} → Sub⋆ (ϕ ,⋆ K) (ψ ,⋆ K)
lifts⋆ σ Z      = ` Z           -- leave newly bound variable untouched
lifts⋆ σ (S α)  = weaken⋆ (σ α) -- apply substitution and weaken
\end{code}

\noindent
Analogously to renaming, we define the action of substitutions on types:

\begin{code}
sub⋆ : ∀ {ϕ ψ} → Sub⋆ ϕ ψ → ∀ {J} → ϕ ⊢⋆ J → ψ ⊢⋆ J
sub⋆ σ (` α)       = σ α
sub⋆ σ (ƛ B)       = ƛ (sub⋆ (lifts⋆ σ) B)
sub⋆ σ (A · B)     = sub⋆ σ A · sub⋆ σ B
sub⋆ σ (A ⇒ B)     = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (Π B)       = Π (sub⋆ (lifts⋆ σ) B)
sub⋆ σ (μ B)       = μ (sub⋆ (lifts⋆ σ) B)
\end{code}

\noindent Substitutions could be implemented as lists of types and
then the \emph{cons} constructor would extend a substitution by an
additional term. Using our functional representation for substitutions
it is convenient to define an operation for this. This effectively
defines a new function that, if it is applied to the \AgdaBound{Z}
variable, returns our additional terms and otherwise invokes the
original substitution.

\begin{code}
extend⋆ : ∀{ϕ ψ} → Sub⋆ ϕ ψ → ∀{J}(A : ψ ⊢⋆ J) → Sub⋆ (ϕ ,⋆ J) ψ
extend⋆ σ A Z      = A    -- project out additional term
extend⋆ σ A (S α)  = σ α  -- apply original substitution
\end{code}

\noindent Substitution of a single type variable is a special case of
parallel substitution \AgdaFunction{sub⋆}. Note we make use of
\AgdaFunction{extend⋆} to define the appropriate substitution by
extending the substitution \AgdaInductiveConstructor{`} with the type
\AgdaBound{A}. Notice that the variable constructor
\AgdaInductiveConstructor{`} serves double duty as the identity
substitution:

\begin{code}
_[_]⋆ : ∀ {ϕ J K} → ϕ ,⋆ K ⊢⋆ J → ϕ ⊢⋆ K → ϕ ⊢⋆ J
B [ A ]⋆ =  sub⋆ (extend⋆ ` A) B
\end{code}

\noindent At this point the reader may well ask how we know that our
substitution and renaming operations are the right ones. One
indication that we have the right definitions is that renaming defines
a functor, and that substitution forms a relative monad. Further,
evaluation (\AgdaFunction{eval} defined in section
\ref{sec:type-normalisation}) can be seen as an algebra of this
relative monad. This categorical structure results in clean proofs.

Additionally, without some sort of compositional structure to our
renaming and substitution, we would be unable to define coherent type
level operations. For example, we must have that performing two
substitutions in sequence results in the same type as performing the
composite of the two substitutions. We assert that these are necessary
functional correctness properties and structure our proofs
accordingly.

Back in our development we show that lifting a renaming and the action
of renaming satisfy the functor laws where \AgdaFunction{lift⋆} and
\AgdaFunction{ren⋆} are both functorial actions.

\begin{code}
lift⋆-id     :  ∀ {ϕ J K}(α : ϕ ,⋆ K ∋⋆ J) → lift⋆ id α ≡ α
lift⋆-comp   : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{ρ' : Ren⋆ ψ Θ}{J K}(α : ϕ ,⋆ K ∋⋆ J)
  → lift⋆ (ρ' ∘ ρ) α ≡ lift⋆ ρ' (lift⋆ ρ α)
  
ren⋆-id    : ∀{ϕ J}(A : ϕ ⊢⋆ J) → ren⋆ id A ≡ A
ren⋆-comp  : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{ρ' : Ren⋆ ψ Θ}{J}(A : ϕ ⊢⋆ J)
  → ren⋆ (ρ' ∘ ρ) A ≡ ren⋆ ρ' (ren⋆ ρ A)
\end{code}
\begin{code}[hide]
-- 1st functor law for lift⋆
lift⋆-id Z     = refl
lift⋆-id (S α) = refl

-- congruence for lift⋆, pointwise equality of renamings
lift⋆-cong : ∀ {ϕ ψ}{σ σ' : Ren⋆ ϕ ψ} → (∀ {J}(α : ϕ ∋⋆ J) → σ α ≡ σ' α)
  → ∀{J K}(α : ϕ ,⋆ J ∋⋆ K) → lift⋆ σ α ≡ lift⋆ σ' α
lift⋆-cong p Z     = refl
lift⋆-cong p (S α) = cong S (p α)

-- congruence for ren⋆, pointwise equality of renamings
ren⋆-cong : ∀ {ϕ ψ}{σ σ' : Ren⋆ ϕ ψ} → (∀ {J}(α : ϕ ∋⋆ J) → σ α ≡ σ' α)
  → ∀{K}(A : ϕ ⊢⋆ K) → ren⋆ σ A ≡ ren⋆ σ' A
ren⋆-cong p (` α)       = cong ` (p α)
ren⋆-cong p (ƛ A)       = cong ƛ (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (A · B)     = cong₂ _·_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (Π A)       = cong Π (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (μ A)       = cong μ (ren⋆-cong (lift⋆-cong p) A)

-- 1st functor law for ren⋆
ren⋆-id (` α)       = refl
ren⋆-id (ƛ A)       = cong ƛ (trans (ren⋆-cong lift⋆-id A) (ren⋆-id A))
ren⋆-id (A · B)     = cong₂ _·_ (ren⋆-id A) (ren⋆-id B)
ren⋆-id (A ⇒ B)     = cong₂ _⇒_ (ren⋆-id A) (ren⋆-id B)
ren⋆-id (Π A)       = cong Π (trans (ren⋆-cong lift⋆-id A) (ren⋆-id A))
ren⋆-id (μ A)       = cong μ (trans (ren⋆-cong lift⋆-id A) (ren⋆-id A))

-- 2nd functor law for lift⋆
lift⋆-comp Z     = refl
lift⋆-comp (S x) = refl

-- 2nd functor law for ren⋆
ren⋆-comp (` α)       = refl
ren⋆-comp (ƛ A)       =
  cong ƛ (trans (ren⋆-cong lift⋆-comp A) (ren⋆-comp A))
ren⋆-comp (A · B)     = cong₂ _·_ (ren⋆-comp A) (ren⋆-comp B)
ren⋆-comp (A ⇒ B)     = cong₂ _⇒_ (ren⋆-comp A) (ren⋆-comp B)
ren⋆-comp (Π A)       =
  cong Π (trans (ren⋆-cong lift⋆-comp A) (ren⋆-comp A))
ren⋆-comp (μ A)       =
  cong μ (trans (ren⋆-cong lift⋆-comp A) (ren⋆-comp A))
\end{code}

\noindent Lifting a substitution satisfies the functor laws where
\AgdaFunction{lift⋆} is a functorial action:

\begin{code}
lifts⋆-id    : ∀ {ϕ J K}(x : ϕ ,⋆ K ∋⋆ J) → lifts⋆ ` x ≡ ` x 
lifts⋆-comp  : ∀{ϕ ψ Θ}{σ : Sub⋆ ϕ ψ}{σ' : Sub⋆ ψ Θ}{J K}(α : ϕ ,⋆ K ∋⋆ J)
  → lifts⋆ (sub⋆ σ' ∘ σ) α ≡ sub⋆ (lifts⋆ σ') (lifts⋆ σ α)
\end{code}

%\noindent
%Various fusion laws about renaming and substitution are needed
%to prove the required properties about substitution:

\begin{code}[hide]
lifts⋆-lift⋆      : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{σ : Sub⋆ ψ Θ}{J K}(α : ϕ ,⋆ K ∋⋆ J)
  → lifts⋆ (σ ∘ ρ) α ≡ lifts⋆ σ (lift⋆ ρ α)
  
sub⋆-ren⋆         : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{σ : Sub⋆ ψ Θ}{J}(A : ϕ ⊢⋆ J)
  → sub⋆ (σ ∘ ρ) A ≡ sub⋆ σ (ren⋆ ρ A)
  
ren⋆-lift⋆-lifts⋆ : ∀{ϕ ψ Θ}{σ : Sub⋆ ϕ ψ}{ρ : Ren⋆ ψ Θ}{J K}(α : ϕ ,⋆ K ∋⋆ J)
  → lifts⋆ (ren⋆ ρ ∘ σ) α ≡ ren⋆ (lift⋆ ρ) (lifts⋆ σ α)
  
ren⋆-sub⋆         : ∀{ϕ ψ Θ}{σ : Sub⋆ ϕ ψ}{ρ : Ren⋆ ψ Θ}{J}(A : ϕ ⊢⋆ J)
  → sub⋆ (ren⋆ ρ ∘ σ) A ≡ ren⋆ ρ (sub⋆ σ A)
\end{code}

\noindent The action of substitution satisfies the relative monad laws
where \AgdaInductiveConstructor{`} is return and \AgdaFunction{sub⋆} is bind:

\begin{code}
sub⋆-id    : ∀ {ϕ J}(A : ϕ ⊢⋆ J) → sub⋆ ` A ≡ A
sub⋆-var   : ∀ {ϕ ψ}{σ : Sub⋆ ϕ ψ}{J}(α : ϕ ∋⋆ J) → sub⋆ σ (` α) ≡ σ α
sub⋆-comp  : ∀{ϕ ψ Θ}{σ : Sub⋆ ϕ ψ}{σ' : Sub⋆ ψ Θ}{J}(A : ϕ ⊢⋆ J)
  → sub⋆ (sub⋆ σ' ∘ σ) A ≡ sub⋆ σ' (sub⋆ σ A)
\end{code}

  \noindent Note that the second law holds definitionally, it is the
first line of the definition of \AgdaFunction{sub⋆}.

\begin{code}[hide]
-- we can push a renaming into an extend⋆
ren⋆-extend⋆ : ∀{Γ Δ}{J K}(ρ : Ren⋆ Γ Δ)(A : Γ ⊢⋆ K)(α : Γ ,⋆ K ∋⋆ J)
  → extend⋆ ` (ren⋆ ρ A) (lift⋆ ρ α) ≡ ren⋆ ρ (extend⋆ ` A α)
  
-- we can push a substitution into an extend⋆
sub⋆-extend⋆ : ∀{Γ Δ}{J K}(σ : Sub⋆ Γ Δ)(A : Γ ⊢⋆ K)(α : Γ ,⋆ K ∋⋆ J)
  → sub⋆ (extend⋆ ` (sub⋆ σ A)) (lifts⋆ σ α) ≡ sub⋆ σ (extend⋆ ` A α)

-- 1st functor law for lifts⋆
lifts⋆-id Z     = refl
lifts⋆-id (S x) = refl

-- congruence for lifts⋆ lifts⋆, pointwise equality on functions
lifts⋆-cong : ∀ {ϕ ψ}
  → {σ σ' : Sub⋆ ϕ ψ}
  → (∀ {J}(α : ϕ ∋⋆ J) → σ α ≡ σ' α)
  → ∀{J K}(α : ϕ ,⋆ K ∋⋆ J)
  → lifts⋆ σ α ≡ lifts⋆ σ' α
lifts⋆-cong p Z     = refl
lifts⋆-cong p (S α) = cong weaken⋆ (p α)

-- congruence for sub⋆, pointwise equality on substitutions
sub⋆-cong : ∀ {ϕ ψ}
  → {σ σ' : Sub⋆ ϕ ψ}
  → (∀ {J}(α : ϕ ∋⋆ J) → σ α ≡ σ' α)
  → ∀{K}(A : ϕ ⊢⋆ K)
  → sub⋆ σ A ≡ sub⋆ σ' A
sub⋆-cong p (` α)       = p α
sub⋆-cong p (ƛ A)       = cong ƛ (sub⋆-cong (lifts⋆-cong p) A)
sub⋆-cong p (A · B)     = cong₂ _·_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (Π A)       = cong Π (sub⋆-cong (lifts⋆-cong p) A)
sub⋆-cong p (μ A)       = cong μ (sub⋆-cong (lifts⋆-cong p) A)

-- 1st monad law for sub⋆ 
sub⋆-id (` x)      = refl
sub⋆-id (ƛ A)      = cong ƛ (trans (sub⋆-cong lifts⋆-id A) (sub⋆-id A))
sub⋆-id (A · B)    = cong₂ _·_ (sub⋆-id A) (sub⋆-id B)
sub⋆-id (A ⇒ B)    = cong₂ _⇒_ (sub⋆-id A) (sub⋆-id B)
sub⋆-id (Π A)      = cong Π (trans (sub⋆-cong lifts⋆-id A) (sub⋆-id A))
sub⋆-id (μ A)      = cong μ (trans (sub⋆-cong lifts⋆-id A) (sub⋆-id A))

-- 2nd rel. monad law for sub⋆ (holds definitionally)
sub⋆-var α = refl

-- fusion for lifts⋆ and lift⋆
lifts⋆-lift⋆ Z     = refl
lifts⋆-lift⋆ (S x) = refl

-- fusion for sub⋆ and ren⋆
sub⋆-ren⋆ (` α)       = refl
sub⋆-ren⋆ (ƛ A)       =
  cong ƛ (trans (sub⋆-cong lifts⋆-lift⋆ A) (sub⋆-ren⋆ A))
sub⋆-ren⋆ (A · B)     = cong₂ _·_ (sub⋆-ren⋆ A) (sub⋆-ren⋆ B)
sub⋆-ren⋆ (A ⇒ B)     = cong₂ _⇒_ (sub⋆-ren⋆ A) (sub⋆-ren⋆ B)
sub⋆-ren⋆ (Π A)       =
  cong Π (trans (sub⋆-cong lifts⋆-lift⋆ A) (sub⋆-ren⋆ A))
sub⋆-ren⋆ (μ A)       =
  cong μ (trans (sub⋆-cong lifts⋆-lift⋆ A) (sub⋆-ren⋆ A))

ren⋆-lift⋆-lifts⋆ Z     = refl
ren⋆-lift⋆-lifts⋆ (S x) = trans (sym (ren⋆-comp _)) (ren⋆-comp _)

-- fusion for ren⋆ and sub⋆
ren⋆-sub⋆ (` α)       = refl
ren⋆-sub⋆ (ƛ A)       =
  cong ƛ (trans (sub⋆-cong ren⋆-lift⋆-lifts⋆ A) (ren⋆-sub⋆ A))
ren⋆-sub⋆ (A · B)     = cong₂ _·_ (ren⋆-sub⋆ A) (ren⋆-sub⋆ B)
ren⋆-sub⋆ (A ⇒ B)     = cong₂ _⇒_ (ren⋆-sub⋆ A) (ren⋆-sub⋆ B)
ren⋆-sub⋆ (Π A)       =
  cong Π (trans (sub⋆-cong ren⋆-lift⋆-lifts⋆ A) (ren⋆-sub⋆ A))
ren⋆-sub⋆ (μ A)       =
  cong μ (trans (sub⋆-cong ren⋆-lift⋆-lifts⋆ A) (ren⋆-sub⋆ A))

-- 2nd functor law for lifts⋆
lifts⋆-comp         Z     = refl
lifts⋆-comp {σ = σ} (S α) = trans (sym (ren⋆-sub⋆ (σ α))) (sub⋆-ren⋆ (σ α))

-- 2nd functor law for sub⋆
sub⋆-comp (` α)       = refl
sub⋆-comp (ƛ A)       = cong ƛ (trans (sub⋆-cong lifts⋆-comp A) (sub⋆-comp A))
sub⋆-comp (A · B)     = cong₂ _·_ (sub⋆-comp A) (sub⋆-comp B)
sub⋆-comp (A ⇒ B)     = cong₂ _⇒_ (sub⋆-comp A) (sub⋆-comp B)
sub⋆-comp (Π A)       = cong Π (trans (sub⋆-cong lifts⋆-comp A) (sub⋆-comp A))
sub⋆-comp (μ A)       = cong μ (trans (sub⋆-cong lifts⋆-comp A) (sub⋆-comp A))

-- pushing a renaming through an extend⋆
ren⋆-extend⋆ ρ A Z     = refl
ren⋆-extend⋆ ρ A (S α) = refl
-- pushing a substitution through an extend⋆
sub⋆-extend⋆ σ A Z     = refl
sub⋆-extend⋆ σ A (S α) = trans (sym (sub⋆-ren⋆ (σ α))) (sub⋆-id (σ α))
\end{code}

\subsection{Type Equality}

\begin{code}[hide]
infix  1 _≡β_
\end{code}

We define type equality as an intrinsically scoped and kinded
relation.  In particular, this means it is impossible to state an
equation between types in different contexts, or of different
kinds. The only interesting rule is the $\beta$-rule from the lambda
calculus. We omit the $\eta$-rule as Plutus Core does not have it. The
formalisation could be easily modified to include it and it would
slightly simplify the type normalisation proof. The additional types
(\AgdaInductiveConstructor{$\Rightarrow$},
\AgdaInductiveConstructor{$\forall$}, and
\AgdaInductiveConstructor{$\mu$}) do not have any computational
behaviour, and are essentially inert.  In particular, the fixed point
operator \AgdaInductiveConstructor{$\mu$} does not complicate the
equational theory.

\begin{code}
data _≡β_ {Φ} : ∀{J} → Φ ⊢⋆ J → Φ ⊢⋆ J → Set where
  β≡β : ∀{K J}(B : Φ ,⋆ J ⊢⋆ K)(A : Φ ⊢⋆ J) → ƛ B · A ≡β B [ A ]⋆
  -- remaining rules hidden
\end{code}
\begin{code}[hide]
  -- structural rules

  refl≡β  : ∀{J}
    → (A : Φ ⊢⋆ J)
      ------------
    → A ≡β A
    
  sym≡β   : ∀{J}{A B : Φ ⊢⋆ J}
    → A ≡β B
      ------
    → B ≡β A
  trans≡β : ∀{J}{A B C : Φ ⊢⋆ J}
    → A ≡β B
    → B ≡β C
      ------
    → A ≡β C

  -- congruence rules

  -- (no variable rule is needed)
 
  ⇒≡β : {A A' B B' : Φ ⊢⋆ *}
    → A ≡β A'
    → B ≡β B'
      ---------------------
    → (A ⇒ B) ≡β (A' ⇒ B')
    
  Π≡β : ∀{J}{B B' : Φ ,⋆ J ⊢⋆ *}
    → B ≡β B'
      -------
    → Π B ≡β Π B'
    
  μ≡β : ∀{B B' : Φ ,⋆ * ⊢⋆ *}
    → B ≡β B'
      -------
    → μ B ≡β μ B'

  ƛ≡β : ∀{K J}{B B' : Φ ,⋆ J ⊢⋆ K}
    → B ≡β B'
      ---------------
    → ƛ B ≡β ƛ B'
    
  ·≡β : ∀{K J}{A A' : Φ ⊢⋆ K ⇒ J}{B B' : Φ ⊢⋆ K}
    → A ≡β A'
    → B ≡β B'
      --------------------
    → A · B ≡β A' · B'    
\end{code}

\noindent We omit the rules for reflexivity, symmetry,
transitivity, and congruence rules for type constructors.


%Note that renaming and substitution preserve type equality:
\begin{code}[hide]
ren⋆≡β : ∀{ϕ ψ J}{A B : ϕ ⊢⋆ J}(ρ : Ren⋆ ϕ ψ)
  → A ≡β B → ren⋆ ρ A ≡β ren⋆ ρ B
sub⋆≡β : ∀{ϕ ψ J}{A B : ϕ ⊢⋆ J}(σ : Sub⋆ ϕ ψ)
  → A ≡β B → sub⋆ σ A ≡β sub⋆ σ B
\end{code}
\begin{code}[hide]
ren⋆≡β ρ (refl≡β A)    = refl≡β (ren⋆ ρ A)
ren⋆≡β ρ (sym≡β p)     = sym≡β (ren⋆≡β ρ p)
ren⋆≡β ρ (trans≡β p q) = trans≡β (ren⋆≡β ρ p) (ren⋆≡β ρ q)
ren⋆≡β ρ (⇒≡β p q)     = ⇒≡β (ren⋆≡β ρ p) (ren⋆≡β ρ q)
ren⋆≡β ρ (Π≡β p)       = Π≡β (ren⋆≡β (lift⋆ ρ) p)
ren⋆≡β ρ (μ≡β p)       = μ≡β (ren⋆≡β (lift⋆ ρ) p)
ren⋆≡β ρ (ƛ≡β p)       = ƛ≡β (ren⋆≡β (lift⋆ ρ) p)
ren⋆≡β ρ (·≡β p q)     = ·≡β (ren⋆≡β ρ p) (ren⋆≡β ρ q)
ren⋆≡β ρ (β≡β B A)     =
  subst (ren⋆ ρ ((ƛ B) · A) ≡β_)
          (trans (sym (sub⋆-ren⋆ B))
                 (trans (sub⋆-cong (ren⋆-extend⋆ ρ A) B)
                        (ren⋆-sub⋆ B)))
          (β≡β _ _)

sub⋆≡β σ (refl≡β A)    = refl≡β (sub⋆ σ A)
sub⋆≡β σ (sym≡β p)     = sym≡β (sub⋆≡β σ p)
sub⋆≡β σ (trans≡β p q) = trans≡β (sub⋆≡β σ p) (sub⋆≡β σ q) 
sub⋆≡β σ (⇒≡β p q)     = ⇒≡β (sub⋆≡β σ p) (sub⋆≡β σ q)
sub⋆≡β σ (Π≡β p)       = Π≡β (sub⋆≡β (lifts⋆ σ) p)
sub⋆≡β σ (μ≡β p)       = μ≡β (sub⋆≡β (lifts⋆ σ) p)
sub⋆≡β σ (ƛ≡β p)       = ƛ≡β (sub⋆≡β (lifts⋆ σ) p)
sub⋆≡β σ (·≡β p q)     = ·≡β (sub⋆≡β σ p) (sub⋆≡β σ q)
sub⋆≡β σ (β≡β B A)     =
  subst (sub⋆ σ ((ƛ B) · A) ≡β_)
        (trans (trans (sym (sub⋆-comp B))
                      (sub⋆-cong (sub⋆-extend⋆ σ A) B))
        (sub⋆-comp B))
        (β≡β _ _)
\end{code}

\subsection{Term contexts}

Having dealt with the type level, we turn our attention to the term level.

\begin{code}[hide]
infix  4 _∋Nf_
infix  3 _⊢Nf_
\end{code}

Terms may contain types, and so the term level contexts must also
track information about type variables in addition to term
variables. We would like to avoid having the extra syntactic baggage
of multiple contexts. We do so by defining term contexts which contain
both (the kinds of) type variables and (the types of) term
variables. Term contexts are indexed over type contexts. In an earlier
version of this formalisation instead of indexing by type contexts we
defined inductive term contexts simultaneously with a recursive
erasure operation that converts a term level context to a type level
context by dropping the term variables but keeping the type
variables. Defining an inductive data type simultaneously with a
recursive function is referred to as \emph{induction recursion}
\cite{induction-recursion}. This proved to be too cumbersome in later
proofs as it can introduce a situation where there can be multiple
provably equal ways to recover the same type context and expressions
become cluttered with proofs of such equations. In addition to the
difficulty of working with this version, it also made type checking
the examples in our formalisation much slower. In the version
presented here neither of these problems arise.

\noindent A context is either empty, or it extends an existing context
by a type variable of a given kind, or by a term variable of a given
type.

\begin{code}
data Ctx : Ctx⋆ → Set where
  ∅    : Ctx ∅
  -- empty term context
  _,⋆_  : ∀{Φ} → Ctx Φ → ∀ J → Ctx (Φ ,⋆ J)
  -- extension by (the kind of) a type variable
  _,_  : ∀ {Φ} → Ctx Φ → Φ ⊢⋆ * → Ctx Φ
  -- extension by (the type of) a term variable
\end{code}

\noindent Let \AgdaBound{Γ}, \AgdaBound{Δ}, range over
contexts.  Note that in the last rule
\AgdaInductiveConstructor{$\_,\_$}, the type we are extending by may
only refer to variables in the type context, a term that inhabits that
type may refer to any variable in its context.

\subsection{Term variables}
\label{sec:term-var}
A variable is indexed by its context and type. While type variables
can appear in types, and those types can appear in terms, the
variables defined here are term level variables only.

Notice that there is only one base constructor
\AgdaInductiveConstructor{Z}. This gives us exactly what we want: we
can only construct term variables. We have two ways to shift these
variables to the left, we use \AgdaInductiveConstructor{S} to shift
over a type and \AgdaInductiveConstructor{T} to shift over a kind in
the context.

\begin{code}
data _∋_ : ∀{Φ} → Ctx Φ → Φ ⊢⋆ * → Set where
  Z : ∀{Φ Γ}  {A : Φ ⊢⋆ *}                         → Γ , A ∋ A
  S : ∀{Φ Γ}  {A : Φ ⊢⋆ *}  {B : Φ ⊢⋆ *}  → Γ ∋ A  → Γ , B ∋ A 
  T : ∀{Φ Γ}  {A : Φ ⊢⋆ *}  {K}           → Γ ∋ A  → Γ ,⋆ K ∋ weaken⋆ A 
\end{code}

\noindent Let \AgdaBound{x}, \AgdaBound{y} range over
variables. Notice that we need weakening of (System $F$) types in the
(Agda) type of \AgdaInductiveConstructor{T}. We must weaken
\AgdaBound{A} to shift it from context \AgdaBound{$\Gamma$} to context
\AgdaBound{$\Gamma$} \AgdaInductiveConstructor{,⋆}
\AgdaBound{K}. Indeed, \AgdaFunction{weaken⋆} is a function and it
appears in a type. This is possible due to the rich support for
dependent types and in particular inductive families in Agda. It is
however a feature that must be used with care and while it often seems
to be the most natural option it can be more trouble than it is
worth. We have learnt from experience, for example, that it is easier
to work with renamings (morphisms between contexts) \AgdaBound{ρ} :
\AgdaFunction{Ren} \AgdaBound{Γ} \AgdaBound{Δ} rather than context
extensions \AgdaBound{Γ} \AgdaFunction{+} \AgdaBound{Δ} where the
contexts are built from concatenation.  The function \AgdaFunction{+},
whose associativity holds only propositionally, is awkward to work
with when it appears in type indices. Renamings do not suffer from
this problem as no additional operations on contexts are needed as we
commonly refer to a renaming into an \emph{arbitrary} new context
(e.g., \AgdaBound{Δ}) rather than, precisely, an extension of an
existing one (e.g., \AgdaBound{Γ} \AgdaFunction{+} \AgdaBound{Δ}).  In
this formalisation we could have chosen to work with explicit
renamings and substitutions turning operations like
\AgdaFunction{weaken⋆} into more benign constructors but this would
have been overall more cumbersome and in this case we are able to work
with executable renaming and substitution cleanly. Doing so cleanly is
a contribution of this work.

\subsection{Terms}
\label{sec:term}

A term is indexed by its context and type.  A term is a variable, an
abstraction, an application, a type abstraction, a type application, a
wrapped term, an unwrapped term, or a term whose type is cast to another 
equal type.

\begin{code}
data _⊢_ {Φ} Γ : Φ ⊢⋆ * → Set where
  `       : ∀{A}    → Γ ∋ A                     → Γ ⊢ A           -- variable
  ƛ       : ∀{A B}  → Γ , A ⊢ B                 → Γ ⊢ A ⇒ B       -- term λ
  _·_     : ∀{A B}  → Γ ⊢ A ⇒ B                 → Γ ⊢ A → Γ ⊢ B   -- term app
  Λ       : ∀{K B}  → Γ ,⋆ K ⊢ B                → Γ ⊢ Π B         -- type λ
  _·⋆_    : ∀{K B}  → Γ ⊢ Π  B  → (A : Φ ⊢⋆ K)  → Γ ⊢ B [ A ]⋆    -- type app
  wrap    : ∀ A     → Γ ⊢ A [ μ A ]⋆            → Γ ⊢ μ A         -- wrap
  unwrap  : ∀{A}    → Γ ⊢ μ A                   → Γ ⊢ A [ μ A ]⋆  -- unwrap
  conv    : ∀{A B}  → A ≡β B    → Γ ⊢ A         → Γ ⊢ B           -- type cast
\end{code}

\noindent Let \AgdaBound{L}, \AgdaBound{M} range over terms. The
last rule \AgdaInductiveConstructor{conv} is required as we have
computation in types. So, a type which has a $\beta$-redex in it is
equal, via type equality, to the type where that redex is reduced. We
want a term which is typed by the original unreduced type to also be
typed by the reduced type. This is a standard typing rule but it looks
strange as a syntactic constructor. See \cite{PTSpaper} for a
discussion of syntax with explicit conversions.

We could give a dynamics for this syntax as a small-step reduction
relation but the \AgdaInductiveConstructor{conv} case is
problematic. It is not enough to say that a conversion reduces if the
underlying term reduces. If a conversion is in the function position
(also called head position) in an application it would block
$\beta$-reduction. We cannot prove progress directly for such a
relation. One could try to construct a dynamics for this system where
during reduction both terms and also types can make reduction steps
and we could modify progress and explicitly prove preservation. We do
not pursue this here. In the system we present here we have the
advantage that the type level language is strongly normalising. In
section \ref{sec:algorithmic} we are able to make use of this
advantage quite directly to solve the conversion problem in a
different way. An additional motivation for us to choose the
normalisation oriented approach is that in Plutus, contracts are
stored and executed on chain with types normalised and this mode of
operation is therefore needed anyway.

If we forget intrinsically typed syntax for a moment and consider
these rules as a type system then we observe that it is not syntax
directed, we cannot use it as the algorithmic specification of a type
checker as we can apply the conversion rule at any point. This is why
we refer to this version of the rules as \emph{declarative} and the
version presented in section \ref{sec:algorithmic}, which is (in
this specific sense) syntax directed, as \emph{algorithmic}.

\section{Algorithmic Rules}
\label{sec:algorithmic}

In this section we remove the conversion rule from our system. Two
promising approaches to achieving this are (1) to push traces of the
conversion rule into the other rules which is difficult to prove
complete \cite{pollack} and (2) to normalise the types which collapses
all the conversion proofs to reflexivity. In this paper we will pursue
the latter.

In the pursuit of (2) we have another important design decision to
make: which approach to take to normalisation. Indeed, another
additional aspect to this is that we need not only a normaliser but a
normal form respecting substitution operation. We choose to implement
a Normalisation-by-Evaluation (NBE) style normaliser and use that to
implement a substitution operation on normal forms.

We chose NBE as we are experienced with it and it has a clear
mathematical structure (e.g., evaluation is a relative algebra for the
relative monad given by substitution) which gave us confidence that we
could construct a well structured normalisation proof that would
compute. The NBE approach is also centred around a normalisation
\emph{algorithm}: something that we want to use. Other approaches
would also work we expect. One option would be to try hereditary
substitutions where the substitution operation is primary and use that
to define a normaliser.

\Cref{sec:normal-types}--\cref{sec:normal-substitution} describe the normal types, the normalisation
algorithm, its correctness proof, and a normalising substitution
operation. Readers not interested in these details may skip to 
\cref{sec:terms-normal-types}.

\subsection{Normal types}
\label{sec:normal-types}

We define a data type of $\beta$-normal types which are either in
constructor form or neutral. Neutral types, which are defined mutually
with normal types, are either variables or (possibly nested)
applications that are stuck on a variable in a function position, so
cannot reduce. In this syntax, it is impossible to define an
expression containing a $\beta$-redex.

\begin{code}[hide]
infix 4 _⊢Nf⋆_
infix 4 _⊢Ne⋆_
\end{code}
\begin{code}
data _⊢Nf⋆_ Φ : Kind → Set

data _⊢Ne⋆_ Φ J : Set where
  `    :          Φ ∋⋆ J                     → Φ ⊢Ne⋆ J  -- type var
  _·_  : ∀{K}  →  Φ ⊢Ne⋆ (K ⇒ J) → Φ ⊢Nf⋆ K  → Φ ⊢Ne⋆ J  -- neutral app

data _⊢Nf⋆_ Φ where
  ƛ    : ∀{K J}  →  Φ ,⋆ K ⊢Nf⋆ J              → Φ ⊢Nf⋆ (K ⇒ J)  -- type lambda
  ne   : ∀{K}    →  Φ ⊢Ne⋆ K                   → Φ ⊢Nf⋆ K        -- neutral type
  _⇒_  :            Φ ⊢Nf⋆ *       → Φ ⊢Nf⋆ *  → Φ ⊢Nf⋆ *        -- function type
  Π    : ∀{K}    →  Φ ,⋆ K ⊢Nf⋆ *              → Φ ⊢Nf⋆ *        -- pi/forall type
  μ    :            Φ ,⋆ * ⊢Nf⋆ *              → Φ ⊢Nf⋆ *        -- recursive type
\end{code}

\noindent Let \AgdaBound{A}, \AgdaBound{B} range over neutral and
normal types.

As before, we need weakening at the type level in the definition of
term level variables. As before, we define it as a special case of
renaming whose correctness we verify by proving the functor laws.

\begin{code}
renNf⋆     : ∀{ϕ ψ} → Ren⋆ ϕ ψ → ∀ {J} → ϕ ⊢Nf⋆ J → ψ ⊢Nf⋆ J
renNe⋆     : ∀{ϕ ψ} → Ren⋆ ϕ ψ → ∀ {J} → ϕ ⊢Ne⋆ J → ψ ⊢Ne⋆ J
weakenNf⋆  : ∀{ϕ J K} → ϕ ⊢Nf⋆ J → ϕ ,⋆ K ⊢Nf⋆ J
\end{code}

\noindent Renaming of normal and neutral types satisfies the functor
laws where \AgdaFunction{renNf⋆} and \AgdaFunction{renNe⋆} are both
functorial actions:

\begin{code}
renNf⋆-id    : ∀{ϕ J}(A : ϕ ⊢Nf⋆ J) → renNf⋆ id A ≡ A
renNf⋆-comp  : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{ρ' : Ren⋆ ψ Θ}{J}(A : ϕ ⊢Nf⋆ J)
  → renNf⋆ (ρ' ∘ ρ) A ≡ renNf⋆ ρ' (renNf⋆ ρ A)

renNe⋆-id    : ∀{ϕ J}(A : ϕ ⊢Ne⋆ J) → renNe⋆ id A ≡ A
renNe⋆-comp  : ∀{ϕ ψ Θ}{ρ : Ren⋆ ϕ ψ}{ρ' : Ren⋆ ψ Θ}{J}(A : ϕ ⊢Ne⋆ J)
  → renNe⋆ (ρ' ∘ ρ) A ≡ renNe⋆ ρ' (renNe⋆ ρ A)
\end{code}

\begin{code}[hide]
renNf⋆ ρ (ƛ B)       = ƛ (renNf⋆ (lift⋆ ρ) B)
renNf⋆ ρ (ne A)      = ne (renNe⋆ ρ A)
renNf⋆ ρ (A ⇒ B)     = renNf⋆ ρ A ⇒ renNf⋆ ρ B
renNf⋆ ρ (Π A)       = Π (renNf⋆ (lift⋆ ρ) A)
renNf⋆ ρ (μ A)       = μ (renNf⋆ (lift⋆ ρ) A)

renNe⋆ ρ (` α)   = ` (ρ α)
renNe⋆ ρ (A · B) = renNe⋆ ρ A · renNf⋆ ρ B

weakenNf⋆ = renNf⋆ S

-- congruence for renNe⋆, pointwise equality of renamings
renNe⋆-cong : ∀ {ϕ ψ}
  → {ρ ρ' : Ren⋆ ϕ ψ}
  → (∀ {J}(α : ϕ ∋⋆ J) → ρ α ≡ ρ' α)
  → ∀{K}(A : ϕ ⊢Ne⋆ K)
    -------------------------
  → renNe⋆ ρ A ≡ renNe⋆ ρ' A

-- congruence for renNf⋆, pointwise equality of renamings
renNf⋆-cong : ∀ {ϕ ψ}
  → {ρ ρ' : Ren⋆ ϕ ψ}
  → (∀ {J}(α : ϕ ∋⋆ J) → ρ α ≡ ρ' α)
  → ∀{K}(A : ϕ ⊢Nf⋆ K)
    ---------------------------
  → renNf⋆ ρ A ≡ renNf⋆ ρ' A
renNf⋆-cong p (ƛ A)       = cong ƛ (renNf⋆-cong (lift⋆-cong p) A)
renNf⋆-cong p (ne A)      = cong ne (renNe⋆-cong p A)
renNf⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (renNf⋆-cong p A) (renNf⋆-cong p B)
renNf⋆-cong p (Π A)       = cong Π (renNf⋆-cong (lift⋆-cong p) A)
renNf⋆-cong p (μ A)       = cong μ (renNf⋆-cong (lift⋆-cong p) A)

-- congruence for renNe⋆, pointwise equality of renamings
renNe⋆-cong p (` α)   = cong ` (p α)
renNe⋆-cong p (A · B) = cong₂ _·_ (renNe⋆-cong p A) (renNf⋆-cong p B)

-- 1st functor law for renNf⋆
renNf⋆-id (ƛ A)       =
  cong ƛ (trans (renNf⋆-cong lift⋆-id A) (renNf⋆-id A))
renNf⋆-id (ne A)      = cong ne (renNe⋆-id A)
renNf⋆-id (A ⇒ B)    = cong₂ _⇒_ (renNf⋆-id A) (renNf⋆-id B)
renNf⋆-id (Π A)       =
  cong Π (trans (renNf⋆-cong lift⋆-id A) (renNf⋆-id A))
renNf⋆-id (μ A)       =
  cong μ (trans (renNf⋆-cong lift⋆-id A) (renNf⋆-id A))

-- 1st functor law for renNe⋆
renNe⋆-id (` α)    = refl
renNe⋆-id (A · B) = cong₂ _·_ (renNe⋆-id A) (renNf⋆-id B)

-- 2nd functor law for renNf⋆
renNf⋆-comp (ƛ A)       = 
  cong ƛ (trans (renNf⋆-cong lift⋆-comp A) (renNf⋆-comp A))
renNf⋆-comp (ne A)      = cong ne (renNe⋆-comp A)
renNf⋆-comp (A ⇒ B)     = cong₂ _⇒_ (renNf⋆-comp A) (renNf⋆-comp B)
renNf⋆-comp (Π A)       =
  cong Π (trans (renNf⋆-cong lift⋆-comp A) (renNf⋆-comp A))
renNf⋆-comp (μ A)       =
  cong μ (trans (renNf⋆-cong lift⋆-comp A) (renNf⋆-comp A))

-- 2nd functor law for renNe⋆
renNe⋆-comp (` α)   = cong ` refl
renNe⋆-comp (A · B) = cong₂ _·_ (renNe⋆-comp A) (renNf⋆-comp B)
\end{code}

\subsection{Type Normalisation algorithm}
\label{sec:type-normalisation}

We use the NBE approach introduced by \cite{nbe}. This is a two stage
process, first we evaluate into a semantic domain that supports open
terms, then we reify these semantic terms back into normal forms.

The semantic domain \AgdaFunction{⊧}, our notion of semantic value is
defined below. Like syntactic types and normal types it is indexed by
context and kind. However, it is not a type defined as an inductive
data type. Instead, it is function that returns a type. More
precisely, it is a function that takes a context and, by recursion on
kinds, defines a new type. At base kind it is defined to be the type
of normal types. At function kind it is either a neutral type at
function kind or a semantic function. If it is a semantic function
then we are essentially interpreting object level (type) functions as
meta level (Agda) functions. The additional renaming argument means we
have a so-called \emph{Kripke function space} (\cite{KripkeLR}). This
is essential for our purposes as it allows us to introduce new free
variables into the context and then apply functions to them. Without
this feature we would not be able to reify from semantic values to
normal forms.

\begin{code}
_⊧_ : Ctx⋆ → Kind → Set
ϕ ⊧ *        = ϕ ⊢Nf⋆ *
ϕ ⊧ (K ⇒ J)  = ϕ ⊢Ne⋆ (K ⇒ J) ⊎ ∀ {ψ} → Ren⋆ ϕ ψ → ψ ⊧ K → ψ ⊧ J
\end{code}

\noindent Let \AgdaBound{V}, \AgdaBound{W} range over values. Let
\AgdaBound{F}, \AgdaBound{G} range over meta-level (Agda)
functions. The definition \AgdaFunction{$\models$} is a Kripke Logical
Predicate. It is also a so-called large elimination, as it is a
function which returns a new type (a \AgdaDatatype{Set} in Agda
terminology). This definition is inspired by Allais et al.
\cite{allias.mcbride.boutillier:neutral}. Their normalisation proof,
which we also took inspiration from, is, in turn, based on the work of
C. Coquand \cite{c.coquand}. The coproduct at the function kind is
present in McBride \cite{mcbride:data}. Our motivation for following
these three approaches was to be careful not to perturb neutral terms
where possible as we want to use our normaliser in substitution and we
want the identity substitution for example not to modify variables. We
also learned from \cite{allias.mcbride.boutillier:neutral} how to move
the uniformity condition out of the definition of values into the
completeness relation.

We will define an evaluator to interpret syntactic types into this
semantic domain but first we need to explain how to reify from
semantics to normal forms. This is needed first as, at base type, our
semantic values are normal forms, so we need a way to convert from
values to normal forms during evaluation. Note that usual NBE
operations of \AgdaFunction{reify} and \AgdaFunction{reflect} are not
mutually defined here as they commonly are in $\beta\eta$-NBE. This is
a characteristic of the coproduct style definition above.

Reflection takes a neutral type and embeds it into a semantic
type. How we do this depends on what kind we are at. At base kind
\AgdaInductiveConstructor{*}, semantic values are normal forms, so we
embed our neutral term using the \AgdaInductiveConstructor{ne}
constructor. At function kind, semantic values are a coproduct of
either a neutral term or a function, so we embed our neutral term
using the \AgdaInductiveConstructor{inl} constructor.

\begin{code}
reflect : ∀{K ϕ} → ϕ ⊢Ne⋆ K → ϕ ⊧ K
reflect {*}      A = ne A
reflect {K ⇒ J}  A = inl A
\end{code}

\noindent Reification is the process of converting from a semantic
type to a normal syntactic type. At base kind and for neutral
functions it is trivial, either we already have a normal form or we
have a neutral term which can be embedded. The last line, where we
have a semantic function is where the action happens. We create a
fresh variable of kind \AgdaBound{K} using \AgdaFunction{reflect} and
apply \AgdaBound{f} to it making use of the Kripke function space by
supplying \AgdaBound{f} with the weakening renaming
\AgdaInductiveConstructor{S}. This creates a semantic value of kind
\AgdaBound{J} in context \AgdaBound{$\Phi$}
\AgdaInductiveConstructor{,} \AgdaBound{K} which we can call
\AgdaFunction{reify} recursively on. This, in turn, gives us a normal
form in \AgdaBound{$\Phi$} \AgdaInductiveConstructor{,} \AgdaBound{K}
\AgdaDatatype{⊢Nf⋆} \AgdaBound{J}. We can then wrap this normal form
in a \AgdaInductiveConstructor{$\lambdabar$}.

\begin{code}
reify : ∀ {K ϕ} → ϕ ⊧ K → ϕ ⊢Nf⋆ K
reify {*}      A         = A
reify {K ⇒ J}  (inl A)   = ne A
reify {K ⇒ J}  (inr F)   = ƛ (reify (F S (reflect (` Z))))
\end{code}

\noindent We define renaming for semantic values. In the semantic
function case, the new renaming is composed with the existing one.

\begin{code}
ren⊧ : ∀ {σ ϕ ψ} → Ren⋆ ϕ ψ → ϕ ⊧ σ → ψ ⊧ σ
ren⊧ {*}      ρ A        = renNf⋆ ρ A
ren⊧ {K ⇒ J}  ρ (inl A)  = inl (renNe⋆ ρ A)
ren⊧ {K ⇒ J}  ρ (inr F)  = inr (λ ρ' →  F (ρ' ∘ ρ))
\end{code}

\noindent Weakening for semantic values is a special case of renaming:

\begin{code}
weaken⊧ : ∀ {σ ϕ K} → ϕ ⊧ σ → (ϕ ,⋆ K) ⊧ σ
weaken⊧ = ren⊧ S
\end{code}

\noindent Our evaluator will take an environment giving semantic
values to syntactic variables, which we represent as a function from
variables to values:

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env ψ ϕ = ∀{J} → ψ ∋⋆ J → ϕ ⊧ J
\end{code}

\noindent Let \AgdaBound{η}, \AgdaBound{η'} range over
environments.

It is convenient to extend an environment with an additional semantic
type:

\begin{code}
extende : ∀{ψ ϕ} → (η : Env ϕ ψ) → ∀{K}(A : ψ ⊧ K) → Env (ϕ ,⋆ K) ψ
extende η V Z      = V
extende η V (S α)  = η α
\end{code}

\noindent Lifting of environments to push them under binders can be
defined as follows. One could also define it analogously to the
lifting of renamings and substitutions defined in
\cref{sec:intrinsically-typed}.

\begin{code}
lifte : ∀ {ϕ ψ} → Env ϕ ψ → ∀ {K} → Env (ϕ ,⋆ K) (ψ ,⋆ K)
lifte η = extende (weaken⊧ ∘ η) (reflect (` Z))
\end{code}

\noindent We define a semantic version of application called
\AgdaFunction{·V} which applies semantic functions to semantic
arguments. As semantic values at function kind can either be neutral
terms or genuine semantic functions we need to pattern match on them
to see how to apply them. Notice that the identity renaming
\AgdaFunction{id} is used in the case of a semantic function. This is
because, as we can read of from the type of \AgdaFunction{$\cdot V$},
the function and the argument are in the same context.

\begin{code}
_·V_ : ∀{ϕ K J} → ϕ ⊧ (K ⇒ J) → ϕ ⊧ K → ϕ ⊧ J
inl A  ·V  V  =  reflect (A · reify V)
inr F  ·V  V  =  F id V
\end{code}

\noindent
Evaluation is defined by recursion on types:

\begin{code}
eval : ∀{ϕ ψ K} → ψ ⊢⋆ K → Env ψ ϕ → ϕ ⊧ K
eval (` α)       η = η α
eval (ƛ B)       η = inr λ ρ v → eval B (extende (ren⊧ ρ ∘ η) v)
eval (A · B)     η = eval A η ·V eval B η
eval (A ⇒ B)     η = reify (eval A η) ⇒ reify (eval B η)
eval (Π B)       η = Π (reify (eval B (lifte η)))
eval (μ B)       η = μ (reify (eval B (lifte η)))
\end{code}

\noindent We can define the identity environment as a function that
embeds variables into neutral terms with \AgdaInductiveConstructor{`}
and then reflects them into values:

\begin{code}
idEnv : ∀ ϕ → Env ϕ ϕ
idEnv ϕ = reflect ∘ `
\end{code}

\noindent We combine \AgdaFunction{reify} with \AgdaFunction{eval} in
the identity environment \AgdaFunction{idEnv} to yield a normalisation
function that takes types in a given context and kind and returns
normal forms in the same context and kind:

\begin{code}
nf : ∀{ϕ K} → ϕ ⊢⋆ K → ϕ ⊢Nf⋆ K
nf A = reify (eval A (idEnv _))
\end{code}

\noindent In the next three sections we prove the three correctness
properties about this normalisation algorithm: completeness;
soundness; and stability.

\subsection{Completeness of Type Normalisation} 

Completeness states that normalising two $\beta$-equal types yields
the same normal form. This is an important correctness property for
normalisation: it ensures that normalisation picks out unique
representatives for normal forms. In a similar way to how we defined
the semantic domain by recursion on kinds, we define a Kripke Logical
Relation on kinds which is a sort of equality on values. At different
kinds and for different semantic values it means different things: at
base type and for neutral functions it means equality of normal forms;
for semantic functions it means that in a new context and given a
suitable renaming into that context, we take related arguments to
related results. We also require an additional condition on semantic
functions, which we call uniformity, following Allais et
al.\cite{allias.mcbride.boutillier:neutral}. However, our definition
is, we believe, simpler as uniformity is just a type synonym (rather
than being mutually defined with the logical relation) and we do not
need to prove any auxiliary lemmas about it throughout the
completeness proof. Uniformity states that if we receive a renaming
and related arguments in the target context of the renaming, and then
a further renaming, we can apply the function at the same context as
the arguments and then rename the result or rename the arguments first
and then apply the function in the later context.

It should not be possible that a semantic function can become equal to
a neutral term so we rule out these cases by defining them to be
\AgdaDatatype{⊥}. This would not be necessary if we were doing
$\beta\eta$-normalisation.

\begin{code}
CR : ∀{ϕ} K → ϕ ⊧ K → ϕ ⊧ K → Set
CR *        A        A'        = A ≡ A'
CR (K ⇒ J)  (inl A)  (inl A')  = A ≡ A'
CR (K ⇒ J)  (inr F)  (inl A')   = ⊥
CR (K ⇒ J)  (inl A)  (inr F')   = ⊥
CR (K ⇒ J)  (inr F)  (inr F')  = Unif F × Unif F' ×
  ∀ {ψ}(ρ : Ren⋆ _ ψ){V V' : ψ ⊧ K} → CR K V V' → CR J (F ρ V) (F' ρ V')
  where
    -- Uniformity
    Unif : ∀{ϕ K J} → (∀ {ψ} → Ren⋆ ϕ ψ → ψ ⊧ K → ψ ⊧ J) → Set
    Unif {ϕ}{K}{J} F = ∀{ψ ψ'}(ρ : Ren⋆ ϕ ψ)(ρ' : Ren⋆ ψ ψ')(V V' : ψ ⊧ K)
      → CR K V V' → CR J (ren⊧ ρ' (F ρ V)) (F (ρ' ∘ ρ) (ren⊧ ρ' V'))
\end{code}

\noindent The relation \AgdaFunction{CR} is not an equivalence
relation, it is only a partial equivalence relation (PER) as
reflexivity does not hold. However, as is always the case for PERs
there is a limited version of reflexivity for elements that are
related to some other element.

\begin{code}
symCR    : ∀{ϕ K}{V V' : ϕ ⊧ K}      → CR K V V' → CR K V' V
transCR  : ∀{ϕ K}{V V' V'' : ϕ ⊧ K}  → CR K V V' → CR K V' V'' → CR K V V''
reflCR   : ∀{ϕ K}{V V' : ϕ ⊧ K}      → CR K V V' → CR K V V
\end{code}
\begin{code}[hide]
symCR {K = *}                         p                 = sym p
symCR {K = K ⇒ J}  {inl A}  {inl A'}  p                 = sym p
symCR {K = K ⇒ J}  {inl A}  {inr F'}  ()
symCR {K = K ⇒ J}  {inr F}  {inl A'}  ()
symCR {K = K ⇒ J}  {inr F}  {inr F'}  (p ,, p' ,, p'')  =
  p' ,, p ,, (λ ρ q → symCR (p'' ρ (symCR q)))

transCR {K = *}                                 p                 q
  = trans p q                                   
transCR {K = K ⇒ J} {inl A} {inl A'} {inl A''}  p                 q
  = trans p q                                   
transCR {K = K ⇒ J} {inl A} {inl A'} {inr A''}  p                 ()
transCR {K = K ⇒ J} {inl A} {inr F'}            ()                q
transCR {K = K ⇒ J} {inr F} {inl A'}            ()                q
transCR {K = K ⇒ J} {inr F} {inr F'} {inl A''}  p                 ()
transCR {K = K ⇒ J} {inr F} {inr F'} {inr F''}  (p ,, p' ,, p'')  (q ,, q' ,, q'') = p ,, q' ,, λ ρ r → transCR (p'' ρ r) (q'' ρ (transCR (symCR r) r))

reflCR p = transCR p (symCR p)
\end{code}

\noindent We think of \AgdaFunction{CR} as equality of semantic
values. Renaming of semantic values \AgdaFunction{ren⊧} (defined in
the section \ref{sec:type-normalisation}) is a functorial action and
we can prove the functor laws. The laws hold up to \AgdaFunction{CR}
not up to propositional equality \AgdaDatatype{≡}:

\begin{code}
ren⊧-id    : ∀{K ϕ}{V V' : ϕ ⊧ K} → CR K V V' → CR K (ren⊧ id V) V'
ren⊧-comp  : ∀{K ϕ ψ Θ}(ρ : Ren⋆ ϕ ψ)(ρ' : Ren⋆ ψ Θ){V V' : ϕ ⊧ K}
  → CR K V V' → CR K (ren⊧ (ρ' ∘ ρ) V) (ren⊧ ρ' (ren⊧ ρ V'))
\end{code}
\begin{code}[hide]
ren⊧-id {*}                          refl = renNf⋆-id _
ren⊧-id {K ⇒ J} {V = inl A} {inl A'} refl = renNe⋆-id _
ren⊧-id {K ⇒ J} {V = inl A} {inr F'} ()
ren⊧-id {K ⇒ J} {V = inr F} {inl A'} () 
ren⊧-id {K ⇒ J} {V = inr F} {inr F'} p    = p

ren⊧-comp {*}     ρ ρ'                  refl             =
  renNf⋆-comp _
ren⊧-comp {K ⇒ J} ρ ρ' {inl A} {inl .A} refl             =
  renNe⋆-comp _
ren⊧-comp {K ⇒ J} ρ ρ' {inl A} {inr F'} ()
ren⊧-comp {K ⇒ J} ρ ρ' {inr F} {inl A'} ()
ren⊧-comp {K ⇒ J} ρ ρ' {inr F} {inr F'} (p ,, p' ,, p'') =
  (λ ρ'' ρ''' v → p (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,,
  (λ ρ'' ρ''' v → p' (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,,
  λ ρ'' q → p'' (ρ'' ∘ ρ' ∘ ρ) q
\end{code}

\noindent The completeness proof follows a similar structure as the
normalisation algorithm. We define \AgdaFunction{reflectCR} and
\AgdaFunction{reifyCR} analogously to the \AgdaFunction{reflect} and
\AgdaFunction{reify} of the algorithm.

\begin{code}
reflectCR  : ∀{ϕ K}{A A' : ϕ ⊢Ne⋆ K}  → A ≡ A'     → CR K (reflect A) (reflect A')
reifyCR    : ∀{ϕ K}{V V' : ϕ ⊧ K}     → CR K V V'  → reify V ≡ reify V'
\end{code}

\begin{code}[hide]
reflectCR {K = *}     p = cong ne p
reflectCR {K = K ⇒ J} p = p

reifyCR {K = *    }                  p                = p
reifyCR {K = K ⇒ J} {inl A} {inl A'} p                = cong ne p
reifyCR {K = K ⇒ J} {inl A} {inr F'} ()             
reifyCR {K = K ⇒ J} {inr F} {inl A'} ()             
reifyCR {K = K ⇒ J} {inr F} {inr F'} (p ,, p' ,, p'') =
  cong ƛ (reifyCR (p'' S (reflectCR refl)))
\end{code}

\noindent We define a pointwise partial equivalence for environments
analogously to the definition of environments themselves:

\begin{code}
EnvCR : ∀ {ϕ ψ} → (η η' : Env ϕ ψ) →  Set
EnvCR η η' = ∀{K}(α : _ ∋⋆ K) → CR K (η α) (η' α) 
\end{code}

\begin{code}[hide]
extendCR : ∀{ϕ ψ K}{η η' : Env ϕ ψ}
  → EnvCR η η'
  → {V V' : ψ ⊧ K}
  → CR K V V'
    ----------------------------
  → EnvCR (extende η V) (extende η' V')
extendCR p q Z      = q
extendCR p q (S α)  = p α

AppCR : ∀{ϕ K J}
  → {V V' : ϕ ⊧ (K ⇒ J)}
  → CR (K ⇒ J) V V'
  → {W W' : ϕ ⊧ K}
  → CR K W W'
  → CR J (V ·V W) (V' ·V W')
AppCR {V = inl A} {inl .A}  refl             q =
  reflectCR (cong (A ·_) (reifyCR q))
AppCR {V = inl A} {inr F'}  ()               q
AppCR {V = inr F} {inl A'}  ()               q
AppCR {V = inr F} {inr F'}  (p ,, p' ,, p'') q = p'' id q
\end{code}

%\noindent We need to be able to push renamings through the
%\AgdaFunction{CR} relation.

\begin{code}[hide]
renCR : ∀{ϕ ψ K}{v v' : ϕ ⊧ K}(ρ : Ren⋆ ϕ ψ)
  → CR K v v' → CR K (ren⊧ ρ v) (ren⊧ ρ v')
\end{code}
\begin{code}[hide]
renCR {K = *}                      ρ p                = cong (renNf⋆ ρ) p
renCR {K = K ⇒ J} {inl A} {inl .A} ρ refl             = refl
renCR {K = K ⇒ J} {inl A} {inr F'} ρ ()
renCR {K = K ⇒ J} {inr F} {inl A'} ρ ()
renCR {K = K ⇒ J} {inr F} {inr F'} ρ (p ,, p' ,, p'') =
  (λ ρ' ρ'' v → p (ρ' ∘ ρ) ρ'' v)
  ,,
  (λ ρ' ρ'' v → p' (ρ' ∘ ρ) ρ'' v)
  ,,
  λ ρ' q → p'' (ρ' ∘ ρ) q
\end{code}

%\noindent We require various properties about renaming interacting
%with other operations:

\begin{code}[hide]
ren⊧-reflect  : ∀{K ϕ ψ}(ρ : Ren⋆ ϕ ψ) A
  → CR K (ren⊧ ρ (reflect A)) (reflect (renNe⋆ ρ A))
ren-reify     : ∀{K ϕ ψ}(ρ : Ren⋆ ϕ ψ){V V'} → CR K V V'
  → renNf⋆ ρ (reify V) ≡ reify (ren⊧ ρ V')
ren⊧·V        : ∀{K J ϕ ψ}(ρ : Ren⋆ ϕ ψ){F F'}{V V'} → CR (K ⇒ J) F F'
  → CR K V V' → CR J (ren⊧ ρ (F ·V V)) (ren⊧ ρ F' ·V ren⊧ ρ V')
\end{code}
\begin{code}[hide]
ren⊧-reflect {*}      ρ A = refl
ren⊧-reflect {K ⇒ J}  ρ A = refl 

ren-reify {*}     ρ                      refl             = refl
ren-reify {K ⇒ J} ρ {V = inl A} {inl .A} refl             = refl
ren-reify {K ⇒ J} ρ {V = inl A} {inr F'} ()            
ren-reify {K ⇒ J} ρ {V = inr F} {inl A'} ()            
ren-reify {K ⇒ J} ρ {V = inr F} {inr F'} (p ,, p' ,, p'') = cong ƛ (trans
  (ren-reify (lift⋆ ρ) (p'' S (reflectCR (refl {x = ` Z}))))
  (reifyCR (transCR
    (p' S (lift⋆ ρ) _ _ (reflectCR refl))
    (AppCR
      {V = ren⊧ (S ∘ ρ) (inr F')}
      {ren⊧ (S ∘ ρ) (inr F')}
      ((λ ρ' ρ'' v → p' (ρ' ∘ S ∘ ρ) ρ'' v)
       ,,
       (λ ρ' ρ'' v → p' (ρ' ∘ S ∘ ρ) ρ'' v)
       ,,
       λ ρ' q → (proj₂ (proj₂ (reflCR (symCR (p ,, p' ,, p''))))
         (ρ' ∘ S ∘ ρ) q))
      (ren⊧-reflect (lift⋆ ρ) (` Z))))))
ren⊧·V {J = *} ρ {inl A} {inl .A} {V}{V'} refl q =
  cong (ne ∘ (renNe⋆ ρ A ·_))
       (trans ( ren-reify ρ (reflCR q)) (reifyCR (renCR ρ q)))
ren⊧·V {J = J ⇒ K} ρ {inl A} {inl .A} refl     q =
  cong (renNe⋆ ρ A ·_)
       (trans ( ren-reify ρ (reflCR q)) (reifyCR (renCR ρ q)))
ren⊧·V ρ {inl A} {inr F}  ()                   q
ren⊧·V ρ {inr F} {inl A'} ()                   q
ren⊧·V ρ {inr F} {inr F'} (p ,, p' ,, p'')     q =
  transCR (p id ρ _ _ q) (p'' ρ (renCR ρ (reflCR (symCR q))))
\end{code}

\noindent Before defining the fundamental theorem of logical relations
which is analogous to \AgdaFunction{eval} we define an identity
extension lemma which is used to bootstrap the fundamental theorem. It
states that if we evaluate a single term in related environments we
get related results. Semantic renaming commutes with
\AgdaFunction{eval}, and we prove this simultaneously with identity
extension:

\begin{code}
idext      : ∀{ϕ ψ K}{η η' : Env ϕ ψ} → EnvCR η η' → (A : ϕ ⊢⋆ K)
  → CR K (eval A η) (eval A η')
ren⊧-eval  : ∀{ϕ ψ Θ K}(A : ψ ⊢⋆ K){η η' : Env ψ ϕ}(p : EnvCR η η')
  → (ρ : Ren⋆ ϕ Θ ) → CR K (ren⊧ ρ (eval A η)) (eval A (ren⊧ ρ ∘ η'))
\end{code}
\begin{code}[hide]
idext p (` α)       = p α
idext p (ƛ B)       =
  (λ ρ ρ' V V' q →
    transCR (ren⊧-eval B (extendCR (renCR ρ ∘ reflCR ∘ p) q) ρ')
            (idext (λ { Z     → renCR ρ' (reflCR (symCR q))
                      ; (S α) → symCR (ren⊧-comp ρ ρ' (reflCR (p α)))})
                   B))
  ,,
  (λ ρ ρ' V V' q →
    transCR
      (ren⊧-eval B (extendCR (renCR ρ ∘ reflCR ∘ symCR ∘ p) q) ρ')
      (idext (λ { Z  → renCR ρ' (reflCR (symCR q))
                ; (S α) → symCR (ren⊧-comp ρ ρ' (reflCR (symCR (p α))))})
             B)) -- first two terms are identical (except for symCR ∘ p))
  ,,
  λ ρ q → idext (extendCR (renCR ρ ∘ p) q) B
idext p (A · B)     = AppCR (idext p A) (idext p B)
idext p (A ⇒ B)     = cong₂ _⇒_ (idext p A) (idext p B)
idext p (Π A)       = cong Π (idext (extendCR (renCR S ∘ p) (reflectCR refl)) A)
idext p (μ A)       = cong μ (idext (extendCR (renCR S ∘ p) refl) A)

ren⊧-eval (` α) p ρ = renCR ρ (p α)
ren⊧-eval (ƛ A) {η}{η'} p ρ =
  (λ ρ' ρ'' V V' q →
    transCR (ren⊧-eval A (extendCR (renCR (ρ' ∘ ρ) ∘ p) q) ρ'')
            (idext (λ { Z     → renCR ρ'' (reflCR (symCR q))
                      ; (S α) → symCR (ren⊧-comp (ρ' ∘ ρ) ρ'' (p α))})
                   A))
  ,,
  (λ ρ' ρ'' V V' q → transCR
    (ren⊧-eval
      A
      (extendCR (renCR ρ' ∘ renCR ρ ∘ reflCR ∘ symCR ∘ p) q) ρ'')
    (idext (λ { Z     → renCR ρ'' (reflCR (symCR q))
              ; (S α) → symCR
                  (ren⊧-comp ρ' ρ'' (renCR ρ (reflCR (symCR (p α)))))})
           A)) -- again two almost identical terms
  ,,
  λ ρ' q → idext (λ { Z → q ; (S α) → ren⊧-comp ρ ρ' (p α) }) A
ren⊧-eval (A · B) p ρ = transCR
  (ren⊧·V ρ (idext (reflCR ∘ p) A) (idext (reflCR ∘ p) B))
  (AppCR (ren⊧-eval A p ρ) (ren⊧-eval B p ρ))
ren⊧-eval (A ⇒ B) p ρ =
  cong₂ _⇒_ (ren⊧-eval A p ρ) (ren⊧-eval B p ρ)
ren⊧-eval (Π A) p ρ =
  cong Π (trans
    (ren⊧-eval A
                    (extendCR (renCR S ∘ p) (reflectCR refl))
                    (lift⋆ ρ))
    (idext (λ{ Z     → ren⊧-reflect (lift⋆ ρ) (` Z)
             ; (S α) → transCR
                  (symCR (ren⊧-comp S (lift⋆ ρ) (reflCR (symCR (p α)))))
                  (ren⊧-comp ρ S (reflCR (symCR (p α))))})
             A))
ren⊧-eval (μ A) p ρ =
  cong μ (trans
    (ren⊧-eval A
                    (extendCR (renCR S ∘ p) refl)
                    (lift⋆ ρ))
    (idext (λ{ Z     → refl
             ; (S α) → transCR
                  (symCR (ren⊧-comp S (lift⋆ ρ) (reflCR (symCR (p α)))))
                  (ren⊧-comp ρ S (reflCR (symCR (p α))))})
             A))
\end{code}

\noindent We have proved that semantic renaming commutes with
evaluation. We also require that syntactic renaming commutes with
evaluation: that we can either rename before evaluation or evaluate in
a renamed environment:

\begin{code}
ren-eval : ∀{ϕ ψ Θ K}(A : Θ ⊢⋆ K){η η' : Env ψ ϕ}(p : EnvCR η η')(ρ : Ren⋆ Θ ψ)
  → CR K (eval (ren⋆ ρ A) η) (eval A (η' ∘ ρ))
\end{code}
\begin{code}[hide]
ren-eval (` α) p ρ = p (ρ α)
ren-eval (ƛ A) p ρ =
  (λ ρ' ρ'' V V' q → transCR
     (ren⊧-eval (ren⋆ (lift⋆ ρ) A) (extendCR (renCR ρ' ∘ reflCR ∘ p) q) ρ'')
     (idext (λ { Z → renCR ρ'' (reflCR (symCR q))
               ; (S α) → symCR (ren⊧-comp ρ' ρ'' (reflCR (p α)))})
            (ren⋆ (lift⋆ ρ) A)))
  ,,
  (λ ρ' ρ'' V V' q → transCR
    (ren⊧-eval A (extendCR (renCR ρ' ∘ reflCR ∘ symCR ∘ p ∘ ρ) q) ρ'')
    (idext (λ { Z     →  renCR ρ'' (reflCR (symCR q))
              ; (S α) → symCR
                   (ren⊧-comp ρ' ρ'' (reflCR (symCR (p (ρ α)))))})
           A))
  ,,
  λ ρ' q → transCR
    (ren-eval A (extendCR (renCR ρ' ∘ p) q) (lift⋆ ρ))
    (idext (λ { Z     → reflCR (symCR q)
              ; (S α) → renCR ρ' (reflCR (symCR (p (ρ α)))) }) A)
ren-eval (A · B) p ρ = AppCR (ren-eval A p ρ) (ren-eval B p ρ)
ren-eval (A ⇒ B) p ρ = cong₂ _⇒_ (ren-eval A p ρ) (ren-eval B p ρ) 
ren-eval (Π A) p ρ =
  cong Π (trans (ren-eval
                  A
                  (extendCR (renCR S ∘ p)
                          (reflectCR (refl {x = ` Z}))) (lift⋆ ρ))
       (idext (λ{ Z     → reflectCR refl
                ; (S α) → (renCR S ∘ reflCR ∘ symCR ∘ p) (ρ α)}) A))
ren-eval (μ A) p ρ =
  cong μ (trans (ren-eval
                  A
                  (extendCR (renCR S ∘ p)
                          refl) (lift⋆ ρ))
       (idext (λ{ Z     → refl
                ; (S α) → (renCR S ∘ reflCR ∘ symCR ∘ p) (ρ α)}) A))
\end{code}

\noindent As in our previous renaming lemma we require that we can
either substitute and then evaluate or, equivalently, evaluate the
underlying term in an environment constructed by evaluating everything
in the substitution. This is the usual \emph{substitution lemma} from
denotational semantics and also one of the laws of an algebra for a
relative monad (the other one holds definitionally):

\begin{code}
subst-eval : ∀{ϕ ψ Θ K}(A : Θ ⊢⋆ K){η η' : Env ψ ϕ}
  → (p : EnvCR η η')(σ : Sub⋆ Θ ψ)
  → CR K (eval (sub⋆ σ A) η) (eval A (λ α → eval (σ α) η'))
\end{code}
\begin{code}[hide]
subst-eval (` α)      p σ = idext p (σ α)
subst-eval (ƛ A)      p σ =
  (λ ρ ρ' v v' q → transCR
     (ren⊧-eval (sub⋆ (lifts⋆ σ) A) (extendCR (renCR ρ ∘ reflCR ∘ p) q) ρ')
     (idext (λ { Z     → renCR ρ' (reflCR (symCR q))
               ; (S α) → symCR (ren⊧-comp ρ ρ' (reflCR (p α)))})
            (sub⋆ (lifts⋆ σ) A)))
  ,,
  (λ ρ ρ' v v' q → transCR
    (ren⊧-eval A (extendCR (renCR ρ ∘ idext (reflCR ∘ symCR ∘ p) ∘ σ) q) ρ')
    (idext (λ { Z → renCR ρ' (reflCR (symCR q))
              ; (S α) → symCR
                   (ren⊧-comp ρ ρ' (idext (reflCR ∘ symCR ∘ p) (σ α)))})
           A))
  ,,
  λ ρ q → transCR (subst-eval A (extendCR (renCR ρ ∘ p) q) (lifts⋆ σ))
    (idext (λ { Z     → reflCR (symCR q)
              ; (S α) → transCR
                   (ren-eval
                     (σ α)
                     (extendCR (renCR ρ ∘ reflCR ∘ symCR ∘ p) (reflCR (symCR q)))
                     S)
                   (symCR (ren⊧-eval (σ α) (reflCR ∘ symCR ∘ p) ρ))})
           A)
subst-eval (A · B)    p σ = AppCR (subst-eval A p σ) (subst-eval B p σ)
subst-eval (A ⇒ B)    p σ = cong₂ _⇒_ (subst-eval A p σ) (subst-eval B p σ)
subst-eval (Π A)      p σ = cong Π (trans
  (subst-eval A (extendCR (renCR S ∘ p) (reflectCR (refl {x = ` Z}))) (lifts⋆ σ))
  (idext (λ{ Z     → reflectCR (refl {x = ` Z})
           ; (S α) → transCR
                (ren-eval
                  (σ α)
                  (extendCR (renCR S ∘ reflCR ∘ symCR ∘ p) (reflectCR refl)) S)
                (symCR (ren⊧-eval (σ α)  (reflCR ∘ symCR ∘ p) S)) })
         A))
subst-eval (μ A)      p σ = cong μ (trans
  (subst-eval A (extendCR (renCR S ∘ p) refl) (lifts⋆ σ))
  (idext (λ{ Z     → reflectCR {K = *} (refl {x = ` Z})
           ; (S α) → transCR
                (ren-eval
                  (σ α)
                  (extendCR (renCR S ∘ reflCR ∘ symCR ∘ p) refl) S)
                (symCR (ren⊧-eval (σ α)  (reflCR ∘ symCR ∘ p) S)) })
         A))
\end{code}

\noindent We can now prove the fundamental theorem of logical
relations for \AgdaFunction{CR}. It is defined by recursion on the
$\beta$-equality proof:

\begin{code}
fund : ∀{ϕ ψ K}{η η' : Env ϕ ψ}{A A' : ϕ ⊢⋆ K}
  → EnvCR η η' → A ≡β A' → CR K (eval A η) (eval A' η')
\end{code}
\begin{code}[hide]
fund p (refl≡β A)          = idext p A
fund p (sym≡β q)           = symCR (fund (symCR ∘ p) q)
fund p (trans≡β q r)       = transCR (fund (reflCR ∘ p) q) (fund p r)
fund p (⇒≡β q r)           = cong₂ _⇒_ (fund p q) (fund p r)
fund p (Π≡β q)             =
  cong Π (fund (extendCR (renCR S ∘ p) (reflectCR refl)) q)
fund p (μ≡β q)             =
  cong μ (fund (extendCR (renCR S ∘ p) refl) q)
fund p (ƛ≡β {B = B}{B'} q) =
  (λ ρ ρ' V V' r → transCR
    (ren⊧-eval B (extendCR (renCR ρ ∘ reflCR ∘ p) r) ρ')
    (idext (λ { Z → renCR ρ' (reflCR (symCR r))
              ; (S α) → symCR (ren⊧-comp ρ ρ' (reflCR (p α)))})
           B))
  ,,
  (λ ρ ρ' V V' r → transCR
     (ren⊧-eval B' (extendCR (renCR ρ ∘ reflCR ∘ symCR ∘ p) r) ρ')
     (idext (λ { Z → renCR ρ' (reflCR (symCR r))
               ; (S α) → symCR (ren⊧-comp ρ ρ' (reflCR (symCR (p α))))})
            B'))
  ,,
  λ ρ r → fund (extendCR (renCR ρ ∘ p) r) q
fund p (·≡β q r) = AppCR (fund p q) (fund p r)
fund p (β≡β B A) =
  transCR (idext (λ { Z     → idext (reflCR ∘ p) A
                    ; (S α) → ren⊧-id (reflCR (p α))})
                 B)
          (symCR (subst-eval B (symCR ∘ p) (extend⋆ ` A)))
\end{code}

\noindent
As for the ordinary identity environment, the proof that the identity
environment is related to itself relies on reflection:

\begin{code}
idCR : ∀{ϕ} → EnvCR (idEnv ϕ) (idEnv ϕ)
idCR x = reflectCR refl
\end{code}

Given all these components we can prove the completeness result by
running the fundamental theorem in the identity environment and then
applying reification. Thus, our normalisation algorithm takes $\beta$-equal
types to identical normal forms.

\begin{code}
completeness : ∀ {K ϕ} {A B : ϕ ⊢⋆ K} → A ≡β B → nf A ≡ nf B
completeness p = reifyCR (fund idCR p)
\end{code}

\noindent Complications due to omitting the $\eta$-rule and the
requirement to avoid extensionality were the main challenges in this
section.

\begin{code}[hide]
-- misc properties
evalCRSubst : ∀{ϕ ψ K}{η η' : Env ϕ ψ}
  → EnvCR η η'
  → {t t' : ϕ ⊢⋆ K}
  → t ≡ t'
  → CR K (eval t η) (eval t' η')
evalCRSubst p {t = t} refl = idext p t
\end{code}


\subsection{Soundness of Type Normalisation}

The soundness property states that terms are $\beta$-equal to their
normal forms which means that normalisation has preserved the
meaning. i.e. that the unique representatives chosen by normalisation
are actually in the equivalence class.

We proceed in a similar fashion to the completeness proof by defining a
logical relation, \AgdaFunction{reify}/\AgdaFunction{reflect},
fundamental theorem, identity environment, and then plugging it all
together to get the required result.

To state the soundness property which relates syntactic types to
normal forms we need to convert normal forms back into syntactic
types:

\begin{code}
embNf  : ∀{Γ K}   → Γ ⊢Nf⋆ K   → Γ ⊢⋆ K
embNe  : ∀{Γ K}   → Γ ⊢Ne⋆ K   → Γ ⊢⋆ K
\end{code}

%\noindent
%We require that embedding commutes with renaming:

\begin{code}[hide]
ren⋆-embNf : ∀{ϕ ψ}(ρ : Ren⋆ ϕ ψ){J}(A : ϕ ⊢Nf⋆ J)
  → embNf (renNf⋆ ρ A) ≡ ren⋆ ρ (embNf A)
ren-embNe : ∀{ϕ ψ}(ρ : Ren⋆ ϕ ψ){J}(A : ϕ ⊢Ne⋆ J)
  → embNe (renNe⋆ ρ A) ≡ ren⋆ ρ (embNe A)

embNf (ƛ A)       = ƛ (embNf A)
embNf (ne A)      = embNe A
embNf (A ⇒ B)     = embNf A ⇒ embNf B
embNf (Π A)       = Π (embNf A)
embNf (μ A)       = μ (embNf A)

embNe (` x)   = ` x
embNe (A · B) = embNe A · embNf B

ren⋆-embNf ρ (ƛ A)       = cong ƛ (ren⋆-embNf (lift⋆ ρ) A)
ren⋆-embNf ρ (ne A)      = ren-embNe ρ A
ren⋆-embNf ρ (A ⇒ B)     = cong₂ _⇒_ (ren⋆-embNf ρ A) (ren⋆-embNf ρ B)
ren⋆-embNf ρ (Π A)       = cong Π (ren⋆-embNf (lift⋆ ρ) A)
ren⋆-embNf ρ (μ A)       = cong μ (ren⋆-embNf (lift⋆ ρ) A)

ren-embNe ρ (` x)    = refl
ren-embNe ρ (n · n') = cong₂ _·_ (ren-embNe ρ n) (ren⋆-embNf ρ n')
\end{code}

\noindent The soundness property is a Kripke Logical relation as
before, defined as a \AgdaDatatype{Set}-valued function by recursion
on kinds. But this time it relates syntactic types and semantic
values. In the first two cases the semantic values are normal or
neutral forms and we can state the property we require easily. In the
last case where we have a semantic function, we would like to state
that sound functions take sound arguments to sound results (modulo the
usual Kripke extension). Indeed, when doing this proof for a version
of the system with $\beta\eta$-equality this was what we needed. Here,
we have only $\beta$-equality for types and we were unable to get the
proof to go through with the same definition. To solve this problem we
added an additional requirement to the semantic function case: we
require that our syntactic type of function kind \AgdaBound{A} is
$\beta$-equal to a $\lambda$-expression. Note this holds trivially if
we have the $\eta$-rule. 

\begin{code}
SR : ∀{ϕ} K → ϕ ⊢⋆ K → ϕ ⊧ K → Set
SR *       A V        = A ≡β embNf V
SR (K ⇒ J) A (inl A') = A ≡β embNe A'
SR (K ⇒ J) A (inr F)  = Σ (_ ,⋆ K ⊢⋆ J) λ A' → (A ≡β ƛ A') ×
  ∀{ψ}(ρ : Ren⋆ _ ψ){B V}
    → SR K B V → SR J (ren⋆ ρ (ƛ A') · B) (ren⊧ ρ (inr F) ·V V)
\end{code}

\noindent As before we have a notion of \AgdaFunction{reify} and
\AgdaFunction{reflect} for soundness. Reflect takes soundness results
about neutral terms to soundness results about semantic values and
reify takes soundness results about semantic values to soundness
results about normal forms:

\begin{code}
reflectSR : ∀{K ϕ}{A : ϕ ⊢⋆ K}{A' : ϕ ⊢Ne⋆ K}
  → A ≡β embNe A' → SR K A (reflect A')
reifySR : ∀{K ϕ}{A : ϕ ⊢⋆ K}{V : ϕ ⊧ K}
  → SR K A V → A ≡β embNf (reify V)
\end{code}
\begin{code}[hide]
reflectSR {*}     p = p
reflectSR {K ⇒ J} p = p

reifySR {*}                 p              = p
reifySR {K ⇒ J} {V = inl A} p              = p
reifySR {K ⇒ J} {V = inr F} (A' ,, p ,, q) =
  trans≡β p (subst (λ B → ƛ B ≡β ƛ (embNf (reify (F S (reflect (` Z))))))
                   (trans (sym (sub⋆-ren⋆ A'))
                          (trans (sub⋆-cong (λ { Z → refl
                                                ; (S x) → refl}) A')
                                 (sub⋆-id A')))
                   (ƛ≡β (trans≡β (sym≡β (β≡β _ _))
                                 (reifySR (q S (reflectSR (refl≡β (` Z))))))))
\end{code}

\noindent We need a notion of environment for soundness, which will be
used in the fundamental theorem. Here it is a lifting of the relation
\AgdaFunction{SR} which relates syntactic types to semantic values to
a relation which relates type substitutions to type environments:

\begin{code}
SREnv : ∀{ϕ ψ} → Sub⋆ ϕ ψ → Env ϕ ψ → Set
SREnv {ϕ} σ η = ∀{K}(α : ϕ ∋⋆ K) → SR K (σ α) (η α)
\end{code}
\begin{code}[hide]
SR,,⋆ : ∀{ϕ ψ}{σ : Sub⋆ ϕ ψ}{η : Env ϕ ψ}
  → SREnv σ η
  → ∀{K}{A : ψ ⊢⋆ K}{V : ψ ⊧ K}
  → SR K A V
  → SREnv (extend⋆ σ A) (extende η V)
SR,,⋆ p q Z     = q
\end{code}

\begin{code}[hide]
SR,,⋆ p q (S α) = p α
renSR : ∀{ϕ ψ}(ρ : Ren⋆ ϕ ψ){K}{A : ϕ ⊢⋆ K}{V : ϕ ⊧ K}
  → SR K A V → SR K (ren⋆ ρ A) (ren⊧ ρ V)
renSR ρ {*}{A}{A'} p = 
  subst (ren⋆ ρ A ≡β_) (sym (ren⋆-embNf ρ A')) (ren⋆≡β ρ p)
renSR ρ {K ⇒ J} {A} {inl A'} p rewrite ren-embNe ρ A' = ren⋆≡β ρ p  
renSR ρ {K ⇒ J} {A} {inr F} (A' ,, p ,, q) =
  ren⋆ (lift⋆ ρ) A'
  ,,
  ren⋆≡β ρ p
  ,,
  λ ρ' {B}{V} r → subst (λ A → SR J (ƛ A · B) (F (ρ' ∘ ρ) V))
                          (trans (ren⋆-cong lift⋆-comp A') (ren⋆-comp A'))
                          (q (ρ' ∘ ρ) r)
\end{code}

\begin{code}[hide]
lifts-extend⋆ : ∀{ϕ ψ K J}
  → (σ : Sub⋆ ϕ ψ)
  → (α : ϕ ,⋆ J ∋⋆ K)
  → lifts⋆ σ α ≡ extend⋆ (weaken⋆ ∘ σ) (` Z) α
lifts-extend⋆ σ Z     = refl
lifts-extend⋆ σ (S _) = refl

substSREnv : ∀{ϕ ψ}{σ σ' : Sub⋆ ϕ ψ}
  → (∀{K}(α : ϕ ∋⋆ K) → σ α ≡ σ' α)
  → {η : Env ϕ ψ}
  → SREnv σ η
    -------------------------------
  → SREnv σ' η
substSREnv p q α rewrite sym (p α) = q α

SRweak : ∀{ϕ ψ}{σ : Sub⋆ ϕ ψ}{η : Env ϕ ψ}
  → SREnv σ η
  → ∀ {K}
    -------------------------------------------------------
  → SREnv (lifts⋆ σ) (extende (ren⊧ S ∘ η) (reflect {K} (` Z)))
SRweak p = substSREnv (sym ∘ lifts-extend⋆ _)
                      (SR,,⋆ (renSR S ∘ p) (reflectSR (refl≡β (` Z)))) 

substSR : ∀{K ϕ}{A A' : ϕ ⊢⋆ K}
  → A' ≡β A
  → {V : ϕ ⊧ K}
  → SR K A V
    ---------------------------
  → SR K A' V
substSR {*}     p         q              = trans≡β p q
substSR {K ⇒ J} p {inl A} q              = trans≡β p q
substSR {K ⇒ J} p {inr F} (A' ,, q ,, r) = _ ,, trans≡β p q ,, r

SRApp : ∀{ϕ K J}
  → {A : ϕ ⊢⋆ (K ⇒ J)}
  → {V : ϕ ⊧ (K ⇒ J)}
  → SR (K ⇒ J) A V
  → {B : ϕ ⊢⋆ K}
  → {W : ϕ ⊧ K}
  → SR K B W
    ---------------------
  → SR J (A · B) (V ·V W)
SRApp {V = inl A} p              q = reflectSR (·≡β (reflectSR p) (reifySR q))
SRApp {V = inr F} (A' ,, p ,, q) r =
  substSR (·≡β (subst
                 (λ B → _ ≡β ƛ B)
                 (trans (sym (ren⋆-id A')) (ren⋆-cong (sym ∘ lift⋆-id) A'))
                 p)
               (refl≡β _))
          (q id r)
\end{code}

\noindent The fundamental Theorem of Logical Relations for
\AgdaFunction{SR} states that, for any type, if we have a related
substitution and environment then the action of the substitution and
environment on the type will also be related.

\begin{code}
evalSR : ∀{ϕ ψ K}(A : ϕ ⊢⋆ K){σ : Sub⋆ ϕ ψ}{η : Env ϕ ψ}
  → SREnv σ η → SR K (sub⋆ σ A) (eval A η)
\end{code}
\begin{code}[hide]
evalSR (` α)                   p = p α
evalSR (Π B)                   p = Π≡β (evalSR B (SRweak p))
evalSR (μ B)                   p = μ≡β (evalSR B (SRweak p))
evalSR (A ⇒ B)                 p = ⇒≡β (evalSR A p) (evalSR B p)
evalSR (ƛ A)   {σ}{η}          p =
  sub⋆ (lifts⋆ σ) A
  ,,
  refl≡β _
  ,,
  λ ρ {B}{V} q → substSR
    (β≡β _ _)
    (subst (λ A' → SR _ A' (eval A (extende (ren⊧ ρ ∘ η) V)))
             (trans (trans (sub⋆-cong (λ
               { Z     → refl
               ; (S α) → trans (trans (sym (sub⋆-id (ren⋆ ρ (σ α))))
                                      (sym (sub⋆-ren⋆ (σ α))))
                               (sub⋆-ren⋆ (σ α))}) A)
                           (sub⋆-comp A))
                    (sub⋆-ren⋆ (sub⋆ (lifts⋆ σ) A)))
             (evalSR A (SR,,⋆ (renSR ρ ∘ p) q)) )
evalSR (A · B)                 p = SRApp (evalSR A p) (evalSR B p)
\end{code}

\noindent The identity substitution is related to the identity environment:

\begin{code}
idSR : ∀{ϕ} → SREnv ` (idEnv ϕ)
idSR = reflectSR ∘ refl≡β ∘ `
\end{code}

\noindent Soundness result: all types are $\beta$-equal to their normal forms.

\begin{code}
soundness : ∀ {ϕ J} → (A : ϕ ⊢⋆ J) → A ≡β embNf (nf A)
soundness A = subst (_≡β embNf (nf A)) (sub⋆-id A) (reifySR (evalSR A idSR))
\end{code}

Complications in the definition of \AgdaFunction{SR} due to omitting
the $\eta$-rule were the biggest challenge in this section.

\subsection{Stability of Type Normalisation}

The normalisation algorithm is stable: renormalising a normal form will
not change it.

This property is often omitted from treatments of normalisation. For
us it is crucial as in the substitution algorithm we define in the
next section and in term level definitions we renormalise types.

Stability for normal forms is defined mutually with an auxiliary
property for neutral types:

\begin{code}
stability    : ∀{K ϕ}(A : ϕ ⊢Nf⋆ K) → nf (embNf A) ≡ A
stabilityNe  : ∀{K ϕ}(A : ϕ ⊢Ne⋆ K) → eval (embNe A) (idEnv ϕ) ≡ reflect A
\end{code}

\noindent We omit the proofs which are a simple simultaneous induction
on normal forms and neutral terms.  The most challenging part for us
was getting the right statement of the stability property for neutral
terms.

\begin{code}[hide]
stability (Π B) =
  cong Π (trans (idext (λ { Z → reflectCR refl
                          ; (S α) → ren⊧-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (μ B) =
  cong μ (trans (idext (λ { Z → refl
                          ; (S α) → ren⊧-reflect S (` α)})
                       (embNf B))
                (stability B))
stability (A ⇒ B) = cong₂ _⇒_ (stability A) (stability B)
stability (ƛ B) =
  cong ƛ (trans (reifyCR (idext (λ { Z → reflectCR refl
                                   ; (S α) → ren⊧-reflect S (` α)})
                                (embNf B)))
                (stability B))
stability {*}     (ne A) = stabilityNe A
stability {K ⇒ J} (ne A) = cong reify (stabilityNe A)

stabilityNe (` α)    = refl
stabilityNe (n · n') =
  trans (cong (_·V (eval (embNf n') (idEnv _))) (stabilityNe n))
        (cong (λ n'' → reflect (n · n'')) (stability n'))
\end{code}

Stability is quite a strong property. It guarantees both that
\AgdaFunction{embNf ∘ nf} is idempotent and that \AgdaFunction{nf} is
surjective:

\begin{code}
idempotent : ∀{ϕ K}(A : ϕ ⊢⋆ K)
  → (embNf ∘ nf ∘ embNf ∘ nf) A ≡ (embNf ∘ nf) A
idempotent A = cong embNf (stability (nf A))

surjective : ∀{ϕ K}(A : ϕ ⊢Nf⋆ K) → Σ (ϕ ⊢⋆ K) λ B → nf B ≡ A
surjective A = embNf A ,, stability A
\end{code}

\noindent Note we use double comma \AgdaInductiveConstructor{,,} for
Agda pairs as we used single comma for contexts.

\subsection{Normality preserving Type Substitution}
\label{sec:normal-substitution}

In the previous subsections we defined a normaliser. In this
subsection we will combine the normaliser with our syntactic
substitution operation on types to yield a normality preserving
substitution. This will be used in later sections to define
intrinsically typed terms with normal types. We proceed by working
with similar interface as we did for ordinary substitutions.

Normality preserving substitutions are functions from type variables
to normal forms:

\begin{code}
SubNf⋆ : Ctx⋆ → Ctx⋆ → Set
SubNf⋆ ϕ ψ = ∀ {J} → ϕ ∋⋆ J → ψ ⊢Nf⋆ J
\end{code}

\noindent We can lift a substitution over a new bound variable as
before. This is needed for going under binders.

\begin{code}
liftsNf⋆ : ∀ {ϕ ψ}→ SubNf⋆ ϕ ψ → ∀{K} → SubNf⋆ (ϕ ,⋆ K) (ψ ,⋆ K)
liftsNf⋆ σ Z      =  ne (` Z)
liftsNf⋆ σ (S α)  =  weakenNf⋆ (σ α)
\end{code}

\noindent We can extend a substitution by an additional normal type
analogously to `cons' for lists:

\begin{code}
extendNf⋆ : ∀{ϕ ψ} → SubNf⋆ ϕ ψ → ∀{J}(A : ψ ⊢Nf⋆ J) → SubNf⋆ (ϕ ,⋆ J) ψ
extendNf⋆ σ A Z     = A
extendNf⋆ σ A (S α) = σ α
\end{code}

\noindent We define the action of substitutions on normal types as
follows: first we embed the normal type to be acted on into a
syntactic type, and compose the normalising substitution with
embedding into syntactic types to turn it into an ordinary
substitution, and then use our syntactic substitution operation from
\cref{sec:type-substitution}. This gives us a syntactic type which we
normalise using the normalisation algorithm from
\cref{sec:type-normalisation}. This is not efficient. It has to
traverse the normal type to convert it back to a syntactic type and it
may run the normalisation algorithm on things that contain no
redexes. However as this is a formalisation primarily, efficiency is
not a priority, correctness is.

\begin{code}
subNf⋆ : ∀{ϕ ψ} → SubNf⋆ ϕ ψ → ∀ {J} → ϕ ⊢Nf⋆ J → ψ ⊢Nf⋆ J
subNf⋆ ρ n = nf (sub⋆ (embNf ∘ ρ) (embNf n))
\end{code}

\noindent We verify the same correctness properties of normalising
substitution as we did for ordinary substitution: namely the relative
monad laws. Note that the second law \AgdaFunction{subNf⋆-∋} doesn't
hold definitionally this time.

\begin{code}
subNf⋆-id    : ∀{ϕ J}(A : ϕ ⊢Nf⋆ J) → subNf⋆ (ne ∘ `) A ≡ A
subNf⋆-var   : ∀{ϕ ψ J}(σ : SubNf⋆ ϕ ψ)(α : ϕ ∋⋆ J)
  → subNf⋆ σ (ne (` α)) ≡ σ α
subNf⋆-comp  : ∀{ϕ ψ Θ}(σ : SubNf⋆ ϕ ψ)(σ' : SubNf⋆ ψ Θ){J}(A : ϕ ⊢Nf⋆ J)
  → subNf⋆ (subNf⋆ σ' ∘ σ) A ≡ subNf⋆ σ' (subNf⋆ σ A)
\end{code}

\noindent These properties and the definitions that follow rely on
properties of normalisation and often corresponding properties of
ordinary substitution. E.g. the first law \AgdaFunction{subNf⋆-id}
follows from \AgdaFunction{stability} and \AgdaFunction{sub⋆-id}, the
second law follows directly from \AgdaFunction{stability} (the
corresponding property holds definitionally in the ordinary case), and
the third law follows from \AgdaFunction{soundness}, various
components of \AgdaFunction{completeness} and
\AgdaFunction{sub⋆-comp}.

\begin{code}[hide]
-- 1st relative monad law for subsNf⋆
subNf⋆-id A = trans (cong nf (sub⋆-id (embNf A))) (stability A)
-- 2nd relative monad law for subNf⋆
subNf⋆-var ρ α = stability (ρ α)

-- pulling a nf through a sub⋆ and fusing it with another nf
subNf⋆-nf : ∀{ϕ ψ}(σ : SubNf⋆ ϕ ψ)
  → ∀{J} → (A : ϕ ⊢⋆ J) → nf (sub⋆ (embNf ∘ σ) A) ≡ subNf⋆ σ (nf A)
subNf⋆-nf σ A = trans
  (reifyCR (subst-eval A idCR (embNf ∘ σ)))
  (trans
    (sym
      (reifyCR (fund (λ α → idext idCR (embNf (σ α))) (sym≡β (soundness A)))))
    (sym (reifyCR (subst-eval (embNf (nf A)) idCR (embNf ∘ σ)))))
subNf⋆-comp σ σ' A = trans
  (trans
    (trans
      (reifyCR
        (subst-eval
          (embNf A)
          idCR
          (embNf ∘ nf ∘ sub⋆ (embNf ∘ σ') ∘ embNf ∘ σ)))
      (trans (reifyCR
               (idext
                 (λ α → fund
                   idCR
                   (sym≡β (soundness (sub⋆ (embNf ∘ σ') (embNf (σ α))))))
                 (embNf A)))
             (sym
               (reifyCR
                 (subst-eval
                   (embNf A)
                   idCR
                   (sub⋆ (embNf ∘ σ') ∘ embNf ∘ σ))))))
  (cong nf (sub⋆-comp (embNf A)))) (subNf⋆-nf σ' (sub⋆ (embNf ∘ σ) (embNf A)))
\end{code}
\begin{code}[hide]
-- renNf⋆ commutes with subNf⋆
renNf⋆-subNf⋆ : ∀{ϕ ψ Θ}(σ : SubNf⋆ ϕ ψ)(ρ : Ren⋆ ψ Θ){J}(A : ϕ ⊢Nf⋆ J)
  → subNf⋆ (renNf⋆ ρ ∘ σ) A ≡ renNf⋆ ρ (subNf⋆ σ A)
renNf⋆-subNf⋆ σ ρ A = trans
  (reifyCR
    (transCR
      (transCR
        (subst-eval (embNf A) idCR (embNf ∘ renNf⋆ ρ ∘ σ))
        (transCR
          (idext
            (λ α → transCR
              (evalCRSubst idCR (ren⋆-embNf ρ (σ α)))
              (transCR
                (ren-eval (embNf (σ α)) idCR ρ)
                (idext (symCR ∘ ren⊧-reflect ρ ∘ `) (embNf (σ α)))))
            (embNf A))
          (symCR (subst-eval (embNf A) (renCR ρ ∘ idCR) (embNf ∘ σ)))))
      (symCR (ren⊧-eval (sub⋆ (embNf ∘ σ) (embNf A)) idCR ρ))))
  (sym (ren-reify ρ (idext idCR (sub⋆ (embNf ∘ σ) (embNf A)))))
\end{code}

\noindent Finally, we define the special case for single type variable
substitution that will be needed in the definition of terms in the
next section:

\begin{code}
_[_]Nf⋆ : ∀{ϕ J K} → ϕ ,⋆ K ⊢Nf⋆ J → ϕ ⊢Nf⋆ K → ϕ ⊢Nf⋆ J
A [ B ]Nf⋆ = subNf⋆ (extendNf⋆ (ne ∘ `) B) A
\end{code}

\noindent The development in this section was straightforward. The
most significant hurdle was that we require a complete normalisation
proof and correctness properties of ordinary substitution to prove
correctness properties of substitution on normal forms. The
substitution algorithm in this section is essentially a rather
indirect implementation of hereditary substitution.

Before moving on we list special case auxiliary lemmas that we will need when
defining renaming and substitution for terms with normal types in
section \ref{sec:operational-semantics}.

\begin{code}
ren[]Nf⋆ : ∀{ϕ Θ J K}(ρ : Ren⋆ ϕ Θ)(A : ϕ ,⋆ K ⊢Nf⋆ J) (B : ϕ ⊢Nf⋆ K )
  → renNf⋆ ρ (A [ B ]Nf⋆) ≡ renNf⋆ (lift⋆ ρ) A [ renNf⋆ ρ B ]Nf⋆

weakenNf⋆-subNf⋆ : ∀{Φ Ψ}(σ : SubNf⋆ Φ Ψ){K}(A : Φ ⊢Nf⋆ *)
  → weakenNf⋆ (subNf⋆ σ A) ≡ subNf⋆ (liftsNf⋆ σ {K = K}) (weakenNf⋆ A)

subNf⋆-liftNf⋆ : ∀{Φ Ψ}(σ : SubNf⋆ Φ Ψ){K}(B : Φ ,⋆ K ⊢Nf⋆ *)
  → subNf⋆ (liftsNf⋆ σ) B
    ≡
    eval (sub⋆ (lifts⋆ (embNf ∘ σ)) (embNf B)) (lifte (idEnv Ψ))

subNf⋆-[]Nf⋆ : ∀{ϕ Ψ K}(σ : SubNf⋆ ϕ Ψ)(A : ϕ ⊢Nf⋆ K)(B : ϕ ,⋆ K ⊢Nf⋆ *)
  → subNf⋆ σ (B [ A ]Nf⋆)
    ≡
    eval (sub⋆ (lifts⋆ (embNf ∘ σ)) (embNf B)) (lifte (idEnv Ψ))
    [ subNf⋆ σ A ]Nf⋆
\end{code}

\begin{code}[hide]
-- Misc properties about subNf

-- congruence for subNf⋆ 
subNf⋆-cong : ∀ {ϕ ψ}
  → {σ σ' : SubNf⋆ ϕ ψ}
  → (∀ {J}(α : ϕ ∋⋆ J) → σ α ≡ σ' α)
  → ∀{K}(A : ϕ ⊢Nf⋆ K)
    -------------------------------
  → subNf⋆ σ A ≡ subNf⋆ σ' A
subNf⋆-cong p A =
  reifyCR (evalCRSubst idCR (sub⋆-cong (cong embNf ∘ p) (embNf A)))

weakenNf⋆-renNf⋆ : ∀ {Φ Ψ}
  → (ρ⋆ : Ren⋆ Φ Ψ)
  → ∀{K}
  → (A : Φ ⊢Nf⋆ *)
  → weakenNf⋆ (renNf⋆ ρ⋆ A) ≡ renNf⋆ (lift⋆ ρ⋆ {K = K}) (weakenNf⋆ A)
weakenNf⋆-renNf⋆ ρ⋆ A = trans (sym (renNf⋆-comp _)) (renNf⋆-comp _)

-- subNf⋆ commutes with renNf⋆
subNf⋆-renNf⋆ : ∀{ϕ ψ Θ}
  → (ρ : Ren⋆ ϕ ψ)
  → (σ : SubNf⋆ ψ Θ)
  → ∀{J}(A : ϕ ⊢Nf⋆ J)
    --------------------------------------
  → subNf⋆ (σ ∘ ρ) A ≡ subNf⋆ σ (renNf⋆ ρ A)
subNf⋆-renNf⋆ ρ σ A = reifyCR
  (evalCRSubst
    idCR
    (trans (sub⋆-ren⋆ (embNf A))
           (cong (sub⋆ (embNf ∘ σ)) (sym (ren⋆-embNf ρ A)))))

weakenNf⋆-subNf⋆ σ⋆ A = trans
  (sym (renNf⋆-subNf⋆ σ⋆ S A))
  (subNf⋆-renNf⋆ S (liftsNf⋆ σ⋆) A)

-- subNf⋆ commutes with [_]Nf⋆
subNf⋆-[]Nf⋆' : ∀{ϕ Ψ K J}
  → (σ : SubNf⋆ ϕ Ψ)
  → (A : ϕ ⊢Nf⋆ K)
  → (B : ϕ ,⋆ K ⊢Nf⋆ J)
    --------------------------------------------------------------
  → subNf⋆ σ (B [ A ]Nf⋆) ≡ subNf⋆ (liftsNf⋆ σ) B [ subNf⋆ σ A ]Nf⋆
subNf⋆-[]Nf⋆' σ A B = trans
  (sym (subNf⋆-comp (extendNf⋆ (ne ∘ `) A) σ B))
  (trans
    (subNf⋆-cong
      {σ = subNf⋆ σ ∘ extendNf⋆ (ne ∘ `) A}
      {σ' = subNf⋆ (extendNf⋆ (ne ∘ `) (subNf⋆ σ A)) ∘ liftsNf⋆ σ}
      (λ { Z     → sym (subNf⋆-var (extendNf⋆ (ne ∘ `) (subNf⋆ σ A)) Z) 
         ; (S α) → trans
              (trans (subNf⋆-var σ α) (sym (subNf⋆-id (σ α))))
              (subNf⋆-renNf⋆
                S
                (extendNf⋆ (ne ∘ `) (subNf⋆ σ A))
                (σ α))})
      B)
    (subNf⋆-comp  (liftsNf⋆ σ) (extendNf⋆ (ne ∘ `) (subNf⋆ σ A)) B))

-- embNf⋆ commutes with lift
subNf-lemma : ∀{ϕ Ψ K J}
  → (σ : SubNf⋆ ϕ Ψ)
  → (A : ϕ ,⋆ K ⊢⋆ J)
  → sub⋆ (lifts⋆ (embNf ∘ σ)) A ≡ sub⋆ (embNf ∘ liftsNf⋆ σ) A
subNf-lemma σ A =
  sub⋆-cong (λ { Z → refl ; (S α) → sym (ren⋆-embNf S (σ α))}) A

-- repairing a mismatch in how the identity can be constructed
subNf-lemma' : ∀{ϕ K J}
  → (A : ϕ ,⋆ K ⊢⋆ J)
  → nf A ≡ reify (eval A (extende (ren⊧ S ∘ idEnv _) (reflect (` Z))))
subNf-lemma' A = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S α) → symCR (ren⊧-reflect S (` α))}) A)

-- combining the two previous lemmas
subNf⋆-[]Nf⋆ σ A B =
  trans (subNf⋆-[]Nf⋆' σ A B)
        (trans (cong (λ B → nf B [ subNf⋆ σ A ]Nf⋆)
                     (sym (subNf-lemma σ (embNf B))))
               (cong (λ B → B [ subNf⋆ σ A ]Nf⋆)
                     (subNf-lemma' (sub⋆ (lifts⋆ (embNf ∘ σ)) (embNf B)))))

subNf⋆-liftNf⋆ σ⋆ B = trans
  (evalCRSubst idCR (sym (subNf-lemma σ⋆ (embNf B))))
  (subNf-lemma' (sub⋆ (lifts⋆ (embNf ∘ σ⋆)) (embNf B)))

weakenNf⋆[] : ∀ {Φ K}(B : Φ ⊢Nf⋆ K)
        → (A : Φ ⊢Nf⋆ *)
        → A ≡ weakenNf⋆ A [ B ]Nf⋆
weakenNf⋆[] B A = trans
  (trans (sym (stability A))
         (evalCRSubst idCR (sym (sub⋆-id (embNf A)))))
  (subNf⋆-renNf⋆ S (extendNf⋆ (ne ∘ `) B) A)


-- renNf⋆ commutes with [_]Nf⋆
ren[]Nf⋆ ρ A B = trans
  (sym (renNf⋆-subNf⋆ (extendNf⋆ (ne ∘ `) B) ρ A))
  (trans
    (subNf⋆-cong
      {σ = renNf⋆ ρ ∘ extendNf⋆ (ne ∘ `) B}
      {σ' = extendNf⋆ (ne ∘ `) (renNf⋆ ρ B) ∘ lift⋆ ρ}
      (λ { Z → refl ; (S α) → refl})
      A)
    (subNf⋆-renNf⋆ (lift⋆ ρ) (extendNf⋆ (ne ∘ `) (renNf⋆ ρ B)) A))
\end{code}

\subsection{Terms with normal types}
\label{sec:terms-normal-types}

\begin{code}[hide]
infix  4 _∋_
infix  4 _⊢_
infixl 5 _,_
\end{code}

We are now ready to define the algorithmic syntax where terms have
normal types and the problematic conversion rule is not needed.

The definition is largely identical except wherever a syntactic type
appeared before, we have a normal type, wherever an operation on
syntactic types appeared before we have the corresponding operation on
normal types. Note that the kind level remains the same, so we reuse
\AgdaDatatype{Ctx⋆} for example.

\subsubsection{Term Contexts}

Term level contexts are indexed by their type level contexts.

\begin{code}
data CtxNf : Ctx⋆ → Set where
  ∅     :                                   CtxNf ∅
  _,⋆_  : ∀{Φ}  →  CtxNf Φ  →  ∀ J       →  CtxNf (Φ ,⋆ J)
  _,_   : ∀{Φ}  →  CtxNf Φ  →  Φ ⊢Nf⋆ *  →  CtxNf Φ
\end{code}

\noindent Let \AgdaBound{Γ}, \AgdaBound{Δ} range over contexts.

\subsubsection{Term Variables}

Note that in the \AgdaInductiveConstructor{T} case, we are required to
weaken (normal) types.

\begin{code}
data _∋Nf_ : ∀ {Φ} → CtxNf Φ → Φ ⊢Nf⋆ * → Set where
  Z : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}                             →   Γ , A ∋Nf A
  S : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}  →  Γ ∋Nf A   →   Γ , B ∋Nf A
  T : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}{K}             →  Γ ∋Nf A   →   Γ ,⋆ K ∋Nf weakenNf⋆ A
\end{code}

\noindent Let \AgdaBound{x}, \AgdaBound{y} range over variables.

\subsubsection{Terms}

Note the absence of the conversion rule. The types of terms are
unique so it is not possible to coerce a term into a different type.

\begin{code}
data _⊢Nf_ {Φ} Γ : Φ ⊢Nf⋆ * → Set where
  `       : ∀{A}    → Γ ∋Nf A                               → Γ ⊢Nf A
  ƛ       : ∀{A B}  → Γ , A ⊢Nf B                           → Γ ⊢Nf A ⇒ B
  _·_     : ∀{A B}  → Γ ⊢Nf A ⇒ B         → Γ ⊢Nf A         → Γ ⊢Nf B
  Λ       : ∀{K B}  → Γ ,⋆ K ⊢Nf B                          → Γ ⊢Nf Π B
  _·⋆_    : ∀{K B}  → Γ ⊢Nf Π B           → (A : Φ ⊢Nf⋆ K)  → Γ ⊢Nf B [ A ]Nf⋆
  wrap    : ∀ A     → Γ ⊢Nf A [ μ A ]Nf⋆                    → Γ ⊢Nf μ A
  unwrap  : ∀{A}    → Γ ⊢Nf μ A                             → Γ ⊢Nf A [ μ A ]Nf⋆
\end{code}

\noindent Let \AgdaBound{L}, \AgdaBound{M} range over terms.

We now have an intrinsically typed definition of terms with types that
are guaranteed to be normal. By side-stepping the conversion problem
we can define an operational semantics for this syntax which we will
do in section \ref{sec:operational-semantics}. In the next section we
will reflect on the correspondence between this syntax and the syntax
with conversion presented in section \ref{sec:intrinsically-typed}.

We define two special cases of \AgdaFunction{subst} which allow us to
substitute the types of variables or terms by propositionally equal
types. While it is the case that types are now represented uniquely we
still want or need to to prove that two types are equal, especially in
the presence of (Agda) variables, cf., while the natural number 7 has
a unique representation in Agda we still might want to prove that for
any natural numbers \AgdaBound{m} and \AgdaBound{n}, \AgdaBound{m}
\AgdaFunction{+} \AgdaBound{n} \AgdaDatatype{≡} \AgdaBound{n}
\AgdaFunction{+} \AgdaBound{m}.

\begin{code}
conv∋Nf : ∀ {Φ Γ}{A A' : Φ ⊢Nf⋆ *} → A ≡ A' → (Γ ∋Nf A) → Γ ∋Nf A'
conv∋Nf refl α = α

conv⊢ : ∀ {Φ Γ}{A : Φ ⊢⋆ *}{A' : Φ ⊢⋆ *} → A ≡ A' → Γ ⊢ A → Γ ⊢ A'
conv⊢ refl α = α
\end{code}

\noindent We see these operations in in use in section
\ref{sec:operational-semantics}.

\section{Correspondence between declarative and algorithmic type systems}
\label{sec:correspondence}

We now have two versions of the syntax/typing rules. Should we just
throw away the old one and use the new one? No. The first version is
the standard textbook version and the second version is an algorithmic
version suitable for implementation. To reconcile the two we prove the
second version is sound and complete with respect to the first. This
is analogous to proving that a typechecker is sound and complete with
respect to the typing rules. Additionally, we prove that before and
after normalising the type, terms erase to the same untyped terms. The
constructions in this section became significantly simpler and easier
after switching from inductive-recursive term contexts to indexed term
contexts.

There is an interesting parallel here with the metatheory of
Twelf\footnote{We thank an anonymous reviewer for bringing this to our
attention.}. In Twelf, hereditary substitution are central to the
metatheory and the semantics is defined on a version of the syntax
where both types and terms are canonical (i.e. they are
normalised). In our setting only the types are normalised
(viz. canonical). But, the situation is similar: there are two
versions of the syntax, one with a semantics (the canonical system),
and one without (the ordinary system). Martens and Crary\cite{lfinlf}
make the case that the ordinary version is the programmer's interface,
or the external language in compiler terminology, and the canonical
version is the internal language in compiler terminology. In their
setting the payoff is also the same: by moving from a language with
type equivalence to one where types are uniquely represented, the
semantics and metatheory become much simpler.

There is also a parallel with how type checking algorithms are
described in the literature: they are often presented an alternative
set of typing rules and then they are proved sound and complete with
respect to the original typing rules. We will draw on this analogy in
the rest of this section as our syntaxes are also type systems.

\subsection{Soundness of Typing}

From a typing point of view, soundness states that anything typeable
in the new type system is also typeable in the old one. From our
syntactic point of view this corresponds to taking an algorithmic term
and embedding it back into a declarative term.

We have already defined an operation to embed normal types into
syntactic types. But, we need an additional operation here: term
contexts contain types so we must embed term contexts with normal type
into term contexts with syntactic types.

\begin{code}
embCtx : ∀{Φ} → CtxNf Φ → Ctx Φ
embCtx ∅          = ∅
embCtx (Γ ,⋆ K)   = embCtx Γ ,⋆ K
embCtx (Γ , A)    = embCtx Γ , embNf A
\end{code}
\begin{code}[hide]
lemT' : ∀{Γ Γ' J K}(A :  Γ ⊢Nf⋆ K)
 → (p : Γ ≡ Γ')
 → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
  → weaken⋆ (subst (_⊢⋆ K) p (embNf A))
    ≡
    subst (_⊢⋆ K) q (embNf (renNf⋆ S A))
lemT' A refl refl = sym (ren⋆-embNf S A)

conv∋ : ∀ {Φ Γ}{A : Φ ⊢⋆ *}{A' : Φ ⊢⋆ *}
 → A ≡ A' →
 (Γ ∋ A) → Γ ∋ A'
conv∋ refl α = α

embTyVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}
  → Γ ∋Nf A
  → embCtx Γ ∋ embNf A
embTyVar Z     = Z
embTyVar (S α) = S (embTyVar α)
embTyVar {Γ = Γ ,⋆ K} (T {A = A} α) =
  conv∋ (sym (ren⋆-embNf S A)) (T (embTyVar α))

lem-embNf[] : ∀{Γ K}(A : Γ ⊢Nf⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) →
  embNf B [ embNf A ]⋆ ≡β embNf (B [ A ]Nf⋆)
lem-embNf[] A B = subst
  (embNf B [ embNf A ]⋆ ≡β_)
  (cong
    embNf
    (trans
      (trans
        (subst-eval (embNf B) idCR (extend⋆ ` (embNf A)))
        (idext (λ { Z → idext idCR (embNf A)
                  ; (S α) → reflectCR (refl {x = ` α})}) (embNf B)))
      (sym (subst-eval (embNf B) idCR (embNf ∘ extendNf⋆ (ne ∘ `) A)))))
  (soundness (embNf B [ embNf A ]⋆))

lem-embNfμ :  ∀{Γ}(A : Γ ,⋆ * ⊢Nf⋆ *) → 
      embNf (A [ μ A ]Nf⋆)
      ≡β
      embNf A [ μ (embNf A) ]⋆
lem-embNfμ A = subst
  (_≡β embNf A [ μ (embNf A) ]⋆)
  (cong embNf (trans (subst-eval (embNf A) idCR (extend⋆ ` (μ (embNf A)))) (trans (idext (λ { Z → refl ; (S α) → idCR α}) (embNf A)) (sym (subst-eval (embNf A) idCR (embNf ∘ (extendNf⋆ (ne ∘ `) (μ A)))))))) (sym≡β (soundness (embNf A [ μ (embNf A) ]⋆)))
\end{code}

\noindent Embedding for terms takes a term with a normal type and
produces a term with a syntactic type.
\begin{code}
embTy : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → embCtx Γ ⊢ embNf A
\end{code}

\begin{code}[hide]
embTy (` α)   = ` (embTyVar α)
embTy (ƛ t)   = ƛ (embTy t)
embTy (t · u) = embTy t · embTy u
embTy (Λ t)   = Λ (embTy t)
embTy (_·⋆_ {B = B} t A) = conv (lem-embNf[] A B) (embTy t ·⋆ embNf A)
embTy (wrap A L) = wrap (embNf A) (conv (lem-embNfμ A) (embTy L))
embTy (unwrap {A = A} L) = conv (sym≡β (lem-embNfμ A)) (unwrap (embTy L))
\end{code}

\noindent Soundness of typing is a direct corollary of \AgdaFunction{embTy}:

\begin{code}
soundnessT : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → embCtx Γ ⊢ embNf A
soundnessT = embTy
\end{code}

\noindent Soundness gives us one direction of the correspondence
between systems. The other direction is given by completeness.

\subsection{Completeness of Typing}

Completeness of typing states that anything typeable by the original
declarative system is typeable by the new system, i.e. we do not lose
any well typed programs by moving to the new system. From our
syntactic point of view, it states that we can take any declarative
term of a given type and normalise its type to produce an algorithmic
term with a type that is $\beta$-equal to the type we started with.

We have already defined normalisation for types. Again, we must provide
an operation that normalises a context:

\begin{code}
nfCtx : ∀{Φ} → Ctx Φ → CtxNf Φ
nfCtx ∅         = ∅
nfCtx (Γ ,⋆ K)  = nfCtx Γ ,⋆ K
nfCtx (Γ , A)   = nfCtx Γ , nf A
\end{code}
\begin{code}[hide]

ren-nf : ∀{ϕ ψ K}(σ : Ren⋆ ϕ ψ)(A : ϕ ⊢⋆ K) →
  renNf⋆ σ (nf A) ≡ nf (ren⋆ σ A)
ren-nf σ A = trans
  (ren-reify σ (idext idCR A))
  (reifyCR
    (transCR
      (ren⊧-eval A idCR σ)
      (transCR
        (idext (ren⊧-reflect σ ∘ `) A)
        (symCR (ren-eval A idCR σ))  )))

nfTyVar : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ ∋ A
  → nfCtx Γ ∋Nf nf A
nfTyVar Z = Z
nfTyVar (S α) =  S (nfTyVar α)
nfTyVar {Γ ,⋆ K} (T {A = A} α) = conv∋Nf (ren-nf S A) (T (nfTyVar α))

-- fixing a mismatch with lift
subNf⋆-lemma' : ∀{ϕ K J}
  → (B : ϕ ,⋆ K ⊢⋆ J)
  → nf B ≡ reify (eval B (extende (ren⊧ S ∘ idEnv _) (reflect (` Z))))
subNf⋆-lemma' B = reifyCR
  (idext (λ { Z     → reflectCR refl
            ; (S x) → symCR (ren⊧-reflect S (` x))}) B)

lemΠnf : ∀{Γ K}(B : Γ ,⋆ K ⊢⋆ *) → Π (nf B) ≡ nf (Π B)
lemΠnf B = cong Π (subNf⋆-lemma' B)

lemμnf : ∀{Γ}(B : Γ ,⋆ * ⊢⋆ *) → μ (nf B) ≡ nf (μ B)
lemμnf B = cong μ (subNf⋆-lemma' B)

lem-nfμ : ∀{Γ}(A : Γ ,⋆ * ⊢⋆ *) →
  nf (A [ μ A ]⋆) ≡ nf A [ μ (nf A) ]Nf⋆
lem-nfμ A = trans (subst-eval A idCR (extend⋆ ` (μ A))) (trans (fund (λ { Z → cong μ (fund (λ { Z → refl ; (S α) → renCR S (reflectCR refl)}) (soundness A)) ; (S α) → idCR α}) (soundness A)) (sym (subst-eval (embNf (nf A)) idCR (embNf ∘ extendNf⋆ (ne ∘ `) (μ (nf A))))))


lem[] : ∀{Φ K}(A : Φ ⊢Nf⋆ K)(B : Φ ,⋆ K ⊢Nf⋆ *) →
  B [ A ]Nf⋆ ≡ nf (sub⋆ (extend⋆ ` (embNf A)) (embNf B))
lem[] A B = evalCRSubst idCR (sub⋆-cong (λ {Z → refl;(S α) → refl}) (embNf B)) 

lem[]' : ∀{Φ K}(A : Φ ⊢⋆ K)(B : Φ ,⋆ K ⊢⋆ *) →
 eval B (lifte (idEnv Φ)) [ nf A ]Nf⋆ ≡ nf (sub⋆ (extend⋆ ` A) B)
lem[]' {Γ} A B = trans
  (lem[] (nf A) (eval B (lifte (idEnv _))))
  (cong
    (subst (_⊢Nf⋆ *) refl)
    (trans
      (trans
        (subst-eval
          (embNf (eval B (lifte (idEnv _))))
          idCR
          (extend⋆ ` (embNf (nf A))))
        (trans
          (fund
            (λ x → idext idCR (extend⋆ ` (embNf (nf A)) x))
            (sym≡β (evalSR B (SRweak idSR))))
          (trans
            (subst-eval
              B
              (λ x → idext idCR (extend⋆ ` (embNf (nf A)) x))
              (lifts⋆ `))
            (idext (λ { Z → symCR (fund idCR (soundness A))
                      ; (S α) → idCR α}) B))))
      (sym (subst-eval B idCR (extend⋆ ` A)))))
\end{code}

\noindent We observe at this point (just before we use it) that
conversion is derivable for the algorithmic syntax. It computes:

\begin{code}
conv⊢Nf : ∀ {Φ Γ}{A A' : Φ ⊢Nf⋆ *} → A ≡ A' → Γ ⊢Nf A → Γ ⊢Nf A'
conv⊢Nf refl L = L
\end{code}

\noindent The operation that normalises the types of terms takes a
declarative term and produces an algorithmic term. We omit the
majority of the definition, but include the case for a conversion. In
this case we have a term \AgdaBound{t} of type \AgdaBound{$\Gamma$}
\AgdaDatatype{$\vdash$} \AgdaBound{A} and a proof \AgdaBound{p} that
\AgdaBound{A} \AgdaDatatype{$\equiv_\beta$} \AgdaBound{B}. We require
a term of of type \AgdaBound{$\Gamma$} \AgdaDatatype{⊢Nf}
\AgdaFunction{nf} \AgdaBound{B}. By inductive hypothesis/recursive
call \AgdaFunction{nfType} \AgdaBound{t} : \AgdaBound{$\Gamma$}
\AgdaDatatype{⊢Nf} \AgdaFunction{nf} \AgdaBound{A}. But, via
completeness of normalisation we know that if \AgdaBound{A}
\AgdaDatatype{$\equiv_\beta$} \AgdaBound{B} then \AgdaFunction{nf}
\AgdaBound{B} \AgdaDatatype{$\equiv$} \AgdaFunction{nf} \AgdaBound{A},
so we invoke the conversion function \AgdaFunction{conv⊢Nf}
with the completeness proof and and the recursive call as arguments:

\begin{AgdaSuppressSpace}
\begin{code}
nfType : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → nfCtx Γ ⊢Nf nf A
nfType (conv p t) = conv⊢Nf (completeness p) (nfType t)
\end{code}

$\quad\vdots\quad$ (remaining cases omitted)\\

\begin{code}[hide]
nfType (` α) = ` (nfTyVar α)
nfType (ƛ t) = ƛ (nfType t)
nfType (t · u) = nfType t · nfType u
nfType (Λ {B = B} t)    = conv⊢Nf (lemΠnf B) (Λ (nfType t))
nfType {Γ} (_·⋆_ {B = B} t A) = conv⊢Nf (lem[]' A B) (nfType t ·⋆ nf A)
nfType {Γ} (wrap A L) =
  conv⊢Nf (lemμnf A) (wrap (nf A) (conv⊢Nf (lem-nfμ A) (nfType L)))
nfType {Γ} (unwrap {A = A} L) =
  conv⊢Nf (sym (lem-nfμ A))
         (unwrap (conv⊢Nf (sym (lemμnf A)) (nfType L)))
\end{code}
\end{AgdaSuppressSpace}

\noindent The operation \AgdaFunction{nfType} is not quite the same as
completeness. Additionally we need that the original type is
$\beta$-equal to the new type. This follows from soundness of
normalisation.

\begin{code}
completenessT : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A
  → nfCtx Γ ⊢Nf nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}

\subsection{Erasure}

We have two version of terms, and we can convert from one to the
other. But, how do we know that after conversion, we still have the
\emph{same} term? One answer is to show that that the term before
conversion and the term after conversion both erase to the same
untyped term. First, we define untyped (but intrinsically scoped) λ-terms:

\begin{code}
data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
\end{code}

\noindent Following the pattern of the soundness and completeness
proofs we deal in turn with contexts, variables, and then terms. In
this case erasing a context corresponds to counting the number of term
variables in the context:

\begin{code}
len : ∀{Φ} → Ctx Φ → ℕ
len ∅         = 0
len (Γ ,⋆ K)  = len Γ
len (Γ , A)   = suc (len Γ)
\end{code}

\noindent Erasure for variables converts them to elements of
\AgdaDatatype{Fin}:

\begin{code}
eraseVar : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z      = zero
eraseVar (S α)  = suc (eraseVar α) 
eraseVar (T α)  = eraseVar α
\end{code}

\noindent Erasure for terms is straightforward:

\begin{code}
erase : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → len Γ ⊢
erase (` α)       = ` (eraseVar α)
erase (ƛ L)       = ƛ (erase L) 
erase (L · M)     = erase L · erase M
erase (Λ L)       = erase L
erase (L ·⋆ A)    = erase L
erase (wrap A L)  = erase L
erase (unwrap L)  = erase L
erase (conv p L)  = erase L
\end{code}


\noindent Note that we drop \AgdaFunction{wrap} and
\AgdaFunction{unwrap} when erasing as these special type casts merely
indicate at which isomorphic type we want the term to
considered. Without types \AgdaFunction{wrap} and
\AgdaFunction{unwrap} serve no purpose.

Erasure from algorithmic terms proceeds in the same way as
declarative terms. The only difference is the that there is no case for
\AgdaInductiveConstructor{conv}:

\begin{code}
lenNf       : ∀{Φ} → CtxNf Φ → ℕ
eraseVarNf  : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋Nf A → Fin (lenNf Γ)
eraseNf     : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → lenNf Γ ⊢
\end{code}
\begin{code}[hide]
lenNf ∅         = 0
lenNf (Γ ,⋆ K)  = lenNf Γ
lenNf (Γ , A)   = suc (lenNf Γ)

eraseVarNf Z      = zero
eraseVarNf (S α)  = suc (eraseVarNf α) 
eraseVarNf (T α)  = eraseVarNf α

eraseNf (` α)       = ` (eraseVarNf α)
eraseNf (ƛ L)       = ƛ (eraseNf L) 
eraseNf (L · M)     = eraseNf L · eraseNf M
eraseNf (Λ L)       = eraseNf L
eraseNf (L ·⋆ A)    = eraseNf L
eraseNf (wrap A L)  = eraseNf L
eraseNf (unwrap L)  = eraseNf L
\end{code}

\noindent Having defined erasure for both term representations we
proceed with the proof that normalising types preserves meaning of
terms. We deal with contexts first, then variables, and then
terms. Normalising types in the context preserves the number of term
variables in the context:

\begin{code}
sameLen : ∀ {Φ}(Γ : Ctx Φ) → lenNf (nfCtx Γ) ≡ len Γ
\end{code}
\begin{code}[hide]
sameLen ∅          = refl
sameLen (Γ ,⋆ J)   = sameLen Γ
sameLen (Γ , A)    = cong suc (sameLen Γ)

lemsuc : ∀{n n'}(p : suc n ≡ suc n')(q : n ≡ n')(i : Fin n) →
  suc (subst Fin q i) ≡ subst Fin p (suc i)
lemsuc refl refl i = refl

lemT : ∀{Φ K}{Γ : CtxNf Φ}{A A' : Φ ⊢Nf⋆ *}{A'' : Φ ,⋆ K ⊢Nf⋆ *}
  → (p : weakenNf⋆ {K = K} A ≡ A'')(q : A ≡ A')(x : Γ ∋Nf A)
  → eraseVarNf x ≡ eraseVarNf (conv∋Nf p (T x))
lemT refl refl x = refl

lemT'' : ∀{Φ K}{Γ : Ctx Φ}{A A' : Φ ⊢⋆ *}{A'' : Φ ,⋆ K ⊢⋆ *}
  → (p : weaken⋆ {K = K} A ≡ A'')(q : A ≡ A')(x : Γ ∋ A)
  → eraseVar x ≡ eraseVar (conv∋ p (T x))
lemT'' refl refl x = refl
\end{code}

\noindent The main complication in the proofs about variables and
terms below is that \AgdaFunction{sameLen} appears in the types. It
complicates each case as the \AgdaFunction{subst} prevents things from
computing when its proof argument is not
\AgdaInductiveConstructor{refl}. This can be worked around using
Agda's \emph{with} feature which allows us to abstract over additional
arguments such as those which are stuck. However in this case we would
need to abstract over so many arguments that the proof becomes
unreadable. Instead we prove a simple lemma for each case which
achieves the same as using \emph{with}. We show the simplest instance
\AgdaFunction{lemzero} for the \AgdaInductiveConstructor{Z} variable
which abstracts over proof of \AgdaFunction{sameLen} and replaces it
with an arbitrary proof \AgdaBound{p} that we can pattern match on.

\begin{code}
lemzero : ∀{n n'}(p : suc n ≡ suc n') → zero ≡ subst Fin p zero
lemzero refl = refl

sameVar : ∀{Φ Γ}{A : Φ ⊢⋆ *}(x : Γ ∋ A)
  → eraseVar x ≡ subst Fin (sameLen Γ) (eraseVarNf (nfTyVar x))
sameVar {Γ = Γ , _} Z = lemzero (cong suc (sameLen Γ))
\end{code}
$\quad\vdots\quad$ (remaining cases omitted)\\
\begin{code}[hide]
sameVar {Γ = Γ , _} (S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (sameLen Γ)) (sameLen Γ) (eraseVarNf (nfTyVar x)))
sameVar {Γ = Γ ,⋆ _} (T {A = A} x) = trans
  (sameVar x)
  (cong (subst Fin (sameLen Γ)) (lemT (ren-nf S A) refl (nfTyVar x)))

lemVar : ∀{n n'}(p : n ≡ n')(i : Fin n) →  ` (subst Fin p i) ≡ subst _⊢ p (` i)
lemVar refl i = refl

lemƛ : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : suc n ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)  
lemƛ refl refl t = refl

lem· : ∀{n n'}(p : n ≡ n')(t u : n ⊢)
  → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lemΠ : ∀{Γ K }(B : Γ ,⋆ K ⊢⋆ *) →
       nf (Π B) ≡ Π (nf B)
lemΠ B = cong Π (sym (subNf-lemma' B))

lem-erase : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(p : A ≡ A')(t : Γ ⊢Nf A)
  → eraseNf t ≡ eraseNf (conv⊢Nf p t)
lem-erase refl t = refl
\end{code}

\begin{code}
same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ ⊢ A)
  → erase t ≡ subst _⊢ (sameLen Γ) (eraseNf (nfType t))
\end{code}
\begin{code}[hide]
same {Γ = Γ}(` x) =
  trans (cong ` (sameVar x)) (lemVar (sameLen Γ) (eraseVarNf (nfTyVar x)))
same {Γ = Γ} (ƛ L) = trans
  (cong ƛ (same L))
  (lemƛ (sameLen Γ) (cong suc (sameLen Γ)) (eraseNf (nfType L)))
same {Γ = Γ} (L · M) = trans
  (cong₂ _·_ (same L) (same M))
  (lem· (sameLen Γ) (eraseNf (nfType L)) (eraseNf (nfType M)))
same {Γ = Γ} (Λ {B = B} L) = trans
  (same L)
  (cong (subst _⊢ (sameLen Γ)) (lem-erase (lemΠnf B) (Λ (nfType L))))
same {Γ = Γ} (_·⋆_ {B = B} L A) = trans
  (same L)
  (cong (subst _⊢ (sameLen Γ)) (lem-erase (lem[]' A B) (nfType L ·⋆ nf A)))
same {Γ = Γ} (wrap A L) = trans
  (same L)
  (cong (subst _⊢ (sameLen Γ))
        (trans (lem-erase (lem-nfμ A) (nfType L))
               (lem-erase (lemμnf A) (wrap _ (conv⊢Nf (lem-nfμ A) (nfType L))))))
same {Γ = Γ} (unwrap {A = A} L) = trans
  (same L)
  (cong (subst _⊢ (sameLen Γ))
        (trans (lem-erase (sym (lemμnf A)) (nfType L))
               (lem-erase (sym (lem-nfμ A))
                          (unwrap (conv⊢Nf (sym (lemμnf A)) (nfType L))))))
same {Γ = Γ} (conv p L) = trans
  (same L)
  (cong (subst _⊢ (sameLen Γ)) (lem-erase (completeness p) (nfType L)))
\end{code}

\noindent This result indicates that when normalising the type of a
term we preserve the meaning of the term where the \emph{meaning} of a
term is taken to be the underlying untyped term.

A similar result holds for embedding terms with normal types back into
terms with ordinary type but we omit it here.

\begin{code}[hide]
-- the other direction
same'Len : ∀ {Φ}(Γ : CtxNf Φ) → len (embCtx Γ) ≡ lenNf Γ
same'Len ∅          = refl
same'Len (Γ ,⋆ J)   = same'Len Γ
same'Len (Γ , A)    = cong suc (same'Len Γ)

same'Var : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋Nf A)
  →  eraseVarNf x ≡ subst Fin (same'Len Γ) (eraseVar (embTyVar x))
same'Var {Γ = Γ , _} Z     = lemzero (cong suc (same'Len Γ))
same'Var {Γ = Γ , _} (S x) = trans
  (cong suc (same'Var x))
  (lemsuc (cong suc (same'Len Γ)) (same'Len Γ) (eraseVar (embTyVar x)))
same'Var {Γ = Γ ,⋆ _} (T {A = A} x) = trans
  (same'Var x)
  (cong (subst Fin (same'Len Γ))
        (lemT'' (sym (ren⋆-embNf S A)) refl (embTyVar x)))

same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(L : Γ ⊢Nf A)
  →  eraseNf L ≡ subst _⊢ (same'Len Γ) (erase (embTy L))
same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (eraseVar (embTyVar x)))
same' {Γ = Γ} (ƛ L)      = trans
  (cong ƛ (same' L))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (erase (embTy L)))
same' {Γ = Γ} (L · M)    = trans
  (cong₂ _·_ (same' L) (same' M))
  (lem· (same'Len Γ) (erase (embTy L)) (erase (embTy M)))
same' {Γ = Γ} (Λ L)      = same' L
same' {Γ = Γ} (L ·⋆ A)   = same' L
same' {Γ = Γ} (wrap A L) = same' L
same' {Γ = Γ} (unwrap L) = same' L
\end{code}

\section{Operational Semantics}
\label{sec:operational-semantics}

We will define the operational semantics on the algorithmic
syntax. Indeed, this was the motivation for introducing the
algorithmic syntax: to provide a straightforward way to define the
semantics without having to deal with type equality coercions. The
operational semantics is defined as a call-by-value small-step
reduction relation. The relation is typed so it is not necessary to
prove preservation as it holds intrinsically. We prove progress for
this relation which shows that programs cannot get stuck. As the
reduction relation contains $\beta$-rules we need to implement
substitution for algorithmic terms before proceeding. As we did for
types, we define renaming first and then use it to define
substitution.


\subsection{Renaming for terms}

We index term level renamings/substitutions by their type
level counter parts.

Renamings are functions from term variables to terms. The type of the
output variable is the type of the input variable renamed by the type
level renaming.

\begin{code}
RenNf : ∀ {Φ Ψ} Γ Δ → Ren⋆ Φ Ψ → Set
RenNf Γ Δ ρ = {A : _ ⊢Nf⋆ *} → Γ ∋Nf A → Δ ∋Nf renNf⋆ ρ A
\end{code}

\noindent We can lift a renaming both over a new term variable and
over a new type variable. These operations are needed to push
renamings under binders (\AgdaInductiveConstructor{$\lambda$} and
\AgdaInductiveConstructor{$\Lambda$} respectively).

%In the code below we often omit the propositional equality coercion
%\AgdaFunction{subst} and its equational proof argument preferring to
%show the underlying operation only.

\begin{code}
liftNf : ∀{Φ Ψ Γ Δ}{ρ⋆ : Ren⋆ Φ Ψ} → RenNf Γ Δ ρ⋆
  → {B : Φ ⊢Nf⋆ *} → RenNf (Γ , B) (Δ , renNf⋆ ρ⋆ B) ρ⋆
liftNf ρ Z     = Z
liftNf ρ (S x) = S (ρ x)

⋆liftNf : ∀{Φ Ψ Γ Δ}{ρ⋆ : Ren⋆ Φ Ψ} → RenNf Γ Δ ρ⋆
  → (∀ {K} → RenNf (Γ ,⋆ K) (Δ ,⋆ K) (lift⋆ ρ⋆))
⋆liftNf ρ (T x) = conv∋Nf (trans (sym (renNf⋆-comp _)) (renNf⋆-comp _)) (T (ρ x))
\end{code}

\noindent Next we define the functorial action of renaming on
terms. In the type instantiation, wrap, unwrap cases we need a proof
as this is where substitutions appear in types.

\begin{code}
renNf : ∀ {Φ Ψ Γ Δ}{ρ⋆ : Ren⋆ Φ Ψ} → RenNf Γ Δ ρ⋆
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → Δ ⊢Nf renNf⋆ ρ⋆ A )
renNf ρ (` x)               = ` (ρ x)
renNf ρ (ƛ N)               = ƛ (renNf (liftNf ρ) N)
renNf ρ (L · M)             = renNf ρ L · renNf ρ M 
renNf ρ (Λ N)               = Λ (renNf (⋆liftNf ρ) N)
renNf ρ (_·⋆_ {B = B} t A)  =
  conv⊢Nf (sym (ren[]Nf⋆ _ B A)) (renNf ρ t ·⋆ renNf⋆ _ A)
renNf ρ (wrap A L)          =
  wrap _ (conv⊢Nf (ren[]Nf⋆ _ A (μ A)) (renNf ρ L))
renNf ρ (unwrap {A = A} L)  =
  conv⊢Nf (sym (ren[]Nf⋆ _ A (μ A))) (unwrap (renNf ρ L))
\end{code}

\noindent Weakening by a type is a special case. Another proof is
needed here.

\begin{code}
weakenNf : ∀ {ϕ Γ}{A : ϕ ⊢Nf⋆ *}{B : ϕ ⊢Nf⋆ *} → Γ ⊢Nf A → Γ , B ⊢Nf A
weakenNf {A = A} x =
  conv⊢Nf (renNf⋆-id A) (renNf (conv∋Nf (sym (renNf⋆-id _)) ∘ S) x)
\end{code}

\noindent We can also weaken by a kind:

\begin{code}
⋆weakenNf : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K} → Γ ⊢Nf A → Γ ,⋆ K ⊢Nf weakenNf⋆ A
⋆weakenNf x = renNf T x
\end{code}

\subsection{Substitution}

Substitutions are defined as functions from type variables to
terms. Like renamings they are indexed by their type level
counterpart, which is used in the return type.

\begin{code}
SubNf : ∀ {Φ Ψ} Γ Δ → SubNf⋆ Φ Ψ → Set
SubNf Γ Δ ρ = {A : _ ⊢Nf⋆ *} → Γ ∋Nf A → Δ ⊢Nf subNf⋆ ρ A
\end{code}

\noindent We define lifting of a substitution over a type and a kind so
that we can push substitutions under binders. Agda is not able to
infer the type level normalising substitution in many cases so we
include it explicitly.

\begin{code}[hide]
renVal-reflect : ∀{Φ Ψ K}
  → (ρ : Ren⋆ Φ Ψ)
  → (n : Φ ⊢Ne⋆ K)
    --------------------------------------------------------
  → CR K (ren⊧ ρ (reflect n)) (reflect (renNe⋆ ρ n))
renVal-reflect {K = *}     ρ n = refl
renVal-reflect {K = K ⇒ J} ρ n = refl 
\end{code}

\begin{code}
liftsNf : ∀{Φ Ψ Γ Δ}(σ⋆ : SubNf⋆ Φ Ψ) → SubNf Γ Δ σ⋆
  → {B : _ ⊢Nf⋆ *} → SubNf (Γ , B) (Δ , subNf⋆ σ⋆ B) σ⋆
liftsNf _ σ Z     = ` Z
liftsNf _ σ (S x) = weakenNf (σ x)

⋆liftsNf : ∀{Φ Ψ Γ Δ}(σ⋆ : SubNf⋆ Φ Ψ) → SubNf Γ Δ σ⋆
  → ∀ {K} → SubNf (Γ ,⋆ K) (Δ ,⋆ K) (liftsNf⋆ σ⋆)
⋆liftsNf σ⋆ σ (T {A = A} x) =
  conv⊢Nf (weakenNf⋆-subNf⋆ σ⋆ A) (⋆weakenNf (σ x))
\end{code}

\noindent Having defined lifting we are now ready to define
substitution on terms:

\begin{code}
subNf : ∀{Φ Ψ Γ Δ}(σ⋆ : SubNf⋆ Φ Ψ) → SubNf Γ Δ σ⋆
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → Δ ⊢Nf subNf⋆ σ⋆ A)
subNf σ⋆ σ (` k)                     = σ k
subNf σ⋆ σ (ƛ N)                     = ƛ (subNf σ⋆ (liftsNf σ⋆ σ) N)
subNf σ⋆ σ (L · M)                   = subNf σ⋆ σ L · subNf σ⋆ σ M
subNf σ⋆ σ (Λ {B = B} N)             =
  Λ (conv⊢Nf (subNf⋆-liftNf⋆ σ⋆ B) (subNf (liftsNf⋆ σ⋆) (⋆liftsNf σ⋆ σ) N))
subNf σ⋆ σ (_·⋆_ {B = B} L M)        =
  conv⊢Nf (sym (subNf⋆-[]Nf⋆ σ⋆ M B)) (subNf σ⋆ σ L ·⋆ subNf⋆ σ⋆ M)
subNf σ⋆ σ (wrap A L)                =
  wrap _ (conv⊢Nf (subNf⋆-[]Nf⋆ σ⋆ (μ A) A) (subNf σ⋆ σ L))
subNf σ⋆ σ (unwrap {A = A} L)        =
  conv⊢Nf (sym (subNf⋆-[]Nf⋆ σ⋆ (μ A) A)) (unwrap (subNf σ⋆ σ L)) 
\end{code}

\begin{code}[hide]
extendNf : ∀{Φ Ψ Γ Δ}
  → (σ⋆ : ∀{K} → Φ ∋⋆ K → Ψ ⊢Nf⋆ K)
  → ({A : Φ ⊢Nf⋆ *} → Γ ∋Nf A → Δ ⊢Nf subNf⋆ σ⋆ A)
  → {A : Φ ⊢Nf⋆ *}
  → (t : Δ ⊢Nf subNf⋆ σ⋆ A)
  → ({B : Φ ⊢Nf⋆ *} → Γ , A ∋Nf B → Δ ⊢Nf subNf⋆ σ⋆ B)
extendNf σ⋆ σ t Z     = t
extendNf σ⋆ σ t (S x) = σ x

lem : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}{A : Φ ⊢Nf⋆ K} → (x : Γ ,⋆ K ∋Nf B) → 
  Γ ⊢Nf subNf⋆ (extendNf⋆ (λ x₁ → ne (` x₁)) A) B
lem (T x) = conv⊢Nf (weakenNf⋆[] _ _) (` x)
\end{code}

\noindent We define special cases for single type and term variable
substitution into a term, but omit their long winded and not very
informative definitions.

\begin{code}
_[_]Nf   : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} → Γ , B ⊢Nf A → Γ ⊢Nf B → Γ ⊢Nf A
_⋆[_]Nf  : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}
  → Γ ,⋆ K ⊢Nf B → (A : Φ ⊢Nf⋆ K) → Γ ⊢Nf B [ A ]Nf⋆
\end{code}
\begin{code}[hide]
_[_]Nf {A = A}{B} b a =
  conv⊢Nf
    (subNf⋆-id A)
  (subNf (ne ∘ `)
         (extendNf (ne ∘ `)
                    (conv⊢Nf (sym (subNf⋆-id _)) ∘ `)
                    (conv⊢Nf (sym (subNf⋆-id B)) a))
                  b)
_⋆[_]Nf b A = subNf (extendNf⋆ (ne ∘ `) A) lem b
\end{code}
We now have all the equipment we need to specify small-step reduction.
\subsection{Reduction}

Before defining the reduction relation we define a value predicate
on terms that captures which terms cannot be reduced any
further. We do not wish to perform unnecessary computation so we do
not compute under the binder in the \AgdaInductiveConstructor{ƛ}
case. However, we do want to have the property that when you erase a
value it remains a value. A typed value, after erasure, should
not require any further reduction to become an untyped value. This
gives us a close correspondence between the typed and untyped
operational semantics. So, it is essential in the
\AgdaInductiveConstructor{Λ} and \AgdaInductiveConstructor{wrap} cases
that the bodies are values as both of these constructors are removed
by erasure.

\begin{code}
data Value {Φ}{Γ} :  {A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → Set where
  V-ƛ     : ∀{A B}(L : Γ , A ⊢Nf B)                  → Value (ƛ L)
  V-Λ     : ∀{K B}{L : Γ ,⋆ K ⊢Nf B}      → Value L  → Value (Λ L)
  V-wrap  : ∀{A}{L : Γ ⊢Nf A [ μ A ]Nf⋆}  → Value L  → Value (wrap A L)
\end{code}

\noindent We give the dynamics of the term language as a small-step
reduction relation. The relation is is typed and terms on the left and
right hand side have the same type so it is impossible to violate
preservation. We have two congruence (xi) rules for application and
only one for type application, types are unique so the type argument
cannot reduce. Indeed, no reduction of types is either possible or
needed. There are three computation (beta) rules, one for application,
one for type application and one for recursive types. We allow
reduction in almost any term argument in the xi rules except under a
\AgdaInductiveConstructor{ƛ}. Allowing reduction under
\AgdaInductiveConstructor{Λ} and \AgdaInductiveConstructor{wrap} is
required to ensure that their bodies become values. The value
condition on the function term in rule \AgdaInductiveConstructor{ξ-·₂}
ensures that, in an application, we reduce the function before the
argument. The value condition on the argument in rule
\AgdaInductiveConstructor{β-ƛ} ensures that the our semantics is
call-by-value.

\begin{code}[hide]
infix 2 _—→_
\end{code}
\begin{code}
data _—→_ {Φ}{Γ} : {A : Φ ⊢Nf⋆ *} → (Γ ⊢Nf A) → (Γ ⊢Nf A) → Set where
  ξ-·₁      : ∀{A B}{L L' : Γ ⊢Nf A ⇒ B}{M : Γ ⊢Nf A}
    → L —→ L' → L · M —→ L' · M
  ξ-·₂      : ∀{A B}{V : Γ ⊢Nf A ⇒ B}{M M' : Γ ⊢Nf A}
    → Value V → M —→ M' → V · M —→ V · M'
  ξ-Λ       : ∀{K B}{L L' : Γ ,⋆ K ⊢Nf B}
    → L —→ L' → Λ L —→ Λ L'
  ξ-·⋆      : ∀{K B}{L L' : Γ ⊢Nf Π B}{A : Φ ⊢Nf⋆ K}
    → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  ξ-unwrap  : ∀{A}{L L' : Γ ⊢Nf μ A}
    → L —→ L' → unwrap L —→ unwrap L'
  ξ-wrap  : {A : Φ ,⋆ * ⊢Nf⋆ *}{L L' : Γ ⊢Nf A [ μ A ]Nf⋆}
    → L —→ L' → wrap A L —→ wrap A L'
  β-ƛ       : ∀{A B}{L : Γ , A ⊢Nf B}{M : Γ ⊢Nf A}
    → Value M → ƛ L · M —→ L [ M ]Nf
  β-Λ       : ∀{K B}{L : Γ ,⋆ K ⊢Nf B}{A : Φ ⊢Nf⋆ K}
    → Value L
    → Λ L ·⋆ A —→ L ⋆[ A ]Nf
  β-wrap    : ∀{A}{L : Γ ⊢Nf A [ μ A ]Nf⋆} → Value L
    → unwrap (wrap A L) —→ L
\end{code}

\subsection{Progress and preservation}

The reduction relation is typed. The definition guarantees that the
terms before and after reduction will have the same type. Therefore it
is not necessary to prove type preservation.

Progress captures the property that reduction of terms should not get
stuck, either a term is already a value or it can make a reduction
step. Progress requires proof. We show the proof in complete
detail. In an earlier version of this work when we did not reduce
under \AgdaInductiveConstructor{Λ} and we proved progress directly for
closed terms, i.e. for terms in the empty context. Reducing under the
\AgdaInductiveConstructor{Λ} binder means that we need to reduce in
non-empty contexts so our previous simple approach no longer works.

There are several approaches to solving this including: (1) modifying
term syntax to ensure that the bodies of
\AgdaInductiveConstructor{Λ}-expressions are already in fully reduced
form (the so-called \emph{value restriction}). This means that we need
only make progress in the empty context as no further progress is
necessary when we are in a non-empty context. This has the downside of
changing the language slightly but keeps progress simple; (2) defining
neutral terms (terms whose reduction is blocked by a variable),
proving a version of progress for open terms, observing that there are
no neutral terms in the empty context and deriving progress for closed
terms as a corollary. This has the disadvantage of having to introduce
neutral terms only to rule them out and complicating the progress
proof; (3) observe that \AgdaInductiveConstructor{Λ} only binds type
variables and not term variables and only term variables can block
progress, prove progress for terms in contexts that contain no term
variables and derive closed progress as a simple corollary. We choose
option 3 here as the language remains the same and the progress proof
is relatively unchanged, it just requires an extra condition on the
context. The only cost is an additional predicate on contexts and an
additional lemma.

Before starting the progress proof we need to capture the property of
a context not containing any term variables. Our term contexts are
indexed by type contexts, if we wanted to rule out type variables we
could talk about term contexts indexed by the empty type context, but
we cannot use the same trick for ruling out term variables. So, we use
a recursive predicate on contexts \AgdaFunction{NoVar}. The empty
context satisfies it, a context extended by (the kind of) a type
variable does if the underlying context does, and a context
containing (the type of) a term variable does not.

\begin{code}
NoVar : ∀{Φ} → CtxNf Φ → Set
NoVar ∅       = ⊤
NoVar (Γ ,⋆ J) = NoVar Γ
NoVar (Γ , A)  = ⊥
\end{code}

\noindent We can prove easily that it is impossible to have term variable in a
context containing no term variables. There is only one case and the
property follows by induction on variables:

\begin{code}
noVar : ∀{Φ Γ} → NoVar Γ → {A : Φ ⊢Nf⋆ *}(x : Γ ∋Nf A) → ⊥
noVar p (T x) = noVar p x
\end{code}

\noindent We can now prove progress. The proof is the same as the one
for closed terms, except for the extra argument \AgdaBound{p} :
\AgdaFunction{NoVar} \AgdaBound{Γ}.

\begin{code}
progress : ∀{Φ}{Γ} → NoVar Γ → {A : Φ ⊢Nf⋆ *}(L : Γ ⊢Nf A)
  → Value L ⊎ Σ (Γ ⊢Nf A) λ L' → L —→ L'
\end{code}

\noindent The variable case is impossible.

\begin{code}
progress p (` x) = ⊥-elim (noVar p x)
\end{code}

\noindent Any \AgdaInductiveConstructor{ƛ}-expression is a value as we
do not reduce under the binder.

\begin{code}
progress p (ƛ L)   = inl (V-ƛ L)
\end{code}

\noindent In the application case we first examine the result of the recursive
call on the function term, if it is a value, it must be a
\AgdaInductiveConstructor{ƛ}-expression, so we examine the recursive
call on the argument term. If this is a value then we perform
β-reduction. Otherwise we make the appropriate ξ-step.

\begin{code}
progress p (L · M)    with progress p L
progress p (L · M)    | inl V        with progress p M
progress p (ƛ L · M)  | inl (V-ƛ L)  | inl V          = inr (L [ M ]Nf ,, β-ƛ V)
progress p (L · M)    | inl V        | inr (M' ,, q)  = inr (L · M' ,, ξ-·₂ V q)
progress p (L · M)    | inr (L' ,, q) = inr (L' · M ,, ξ-·₁ q)
\end{code}

\noindent As we must reduce under \AgdaInductiveConstructor{Λ} and
\AgdaInductiveConstructor{wrap} in both cases we make a recursive call
on their bodies and proceed accordingly. Notice that the argument
\AgdaBound{p} is unchanged in the recursive call to the body of a
\AgdaInductiveConstructor{Λ} as \AgdaFunction{NoVar} (\AgdaBound{Γ}
\AgdaInductiveConstructor{,⋆} \AgdaBound{K}) = \AgdaFunction{NoVar}
\AgdaBound{Γ}.

\begin{code}
progress p (Λ L)  with progress p L
...               | inl V          = inl (V-Λ V)
...               | inr (L' ,, q)  = inr (Λ L' ,, ξ-Λ q)
progress p (wrap A L)  with progress p L
...                    | inl V          = inl (V-wrap V)
...                    | inr (L' ,, q)  = inr (wrap A L' ,, ξ-wrap q)
\end{code}

\noindent In the type application case we first examine the result of
recursive call on the type function argument. If it is a value it must
be a \AgdaInductiveConstructor{Λ}-expression and we perform
β-reduction. Otherwise we perform a ξ-step.


\begin{code}
progress p (L ·⋆ A)      with progress p L
progress p (Λ L ·⋆ A)    | inl (V-Λ V)    = inr (L ⋆[ A ]Nf ,, (β-Λ V))
progress p (L ·⋆ A)      | inr (L' ,, q)  = inr (L' ·⋆ A ,, ξ-·⋆ q)
\end{code}

\noindent In the \AgdaInductiveConstructor{unwrap} case we examine the
result of the recursive call on the body. If it is a value it must be
a wrap and we perform β-reduction or a ξ-step otherwise. That
completes the proof. 

\begin{code}
progress p (unwrap L)           with progress p L
progress p (unwrap (wrap A L))  | inl (V-wrap V)  = inr (L ,, β-wrap V)
progress p (unwrap L)           | inr (L' ,, q)   = inr (unwrap L' ,, ξ-unwrap q)
\end{code}

\noindent Progress in the empty context \AgdaFunction{progress∅} is a
simple corollary. The empty context trivially satisfies
\AgdaFunction{NoVar} as \AgdaFunction{NoVar}
\AgdaInductiveConstructor{∅} = \AgdaDatatype{⊤}:

\begin{code}
progress∅ : ∀{A}(L : ∅ ⊢Nf A) → Value L ⊎ Σ (∅ ⊢Nf A) λ L' → L —→ L'
progress∅ = progress tt
\end{code}

\subsection{Erasure}

We can extend our treatment of erasure from
syntax to (operational) semantics. Indeed, when defining values were
careful to ensure this was possible.

\begin{code}[hide]
infix 2 _U—→_
open import Data.List hiding ([_]; map)

RenU : ℕ → ℕ → Set
RenU m n = Fin m → Fin n

liftU : ∀{m n} → RenU m n → RenU (suc m) (suc n)
liftU ρ zero = zero
liftU ρ (suc x) = suc (ρ x)

renU     : ∀{m n} → RenU m n → m ⊢ → n ⊢
renU ρ (` x)          = ` (ρ x)
renU ρ (ƛ t)        = ƛ (renU (liftU ρ) t)
renU ρ (t · u)        = renU ρ t · renU ρ u

liftU-cong : ∀{m n}{ρ ρ' : RenU m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (α : Fin (suc m))
  → liftU ρ α ≡ liftU ρ' α
liftU-cong p zero    = refl
liftU-cong p (suc α) = cong suc (p α)

renU-cong : ∀{m n}{ρ ρ' : RenU m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (t : m ⊢)
  → renU ρ t ≡ renU ρ' t

renU-cong p (` x)          = cong ` (p x)
renU-cong p (ƛ t)        = cong ƛ (renU-cong (liftU-cong p) t)
renU-cong p (t · u)        = cong₂ _·_ (renU-cong p t) (renU-cong p u)

renU-id : ∀{n} → (t : n ⊢) → t ≡ renU id t

liftU-id : ∀{n} → (α : Fin (suc n)) → id α ≡ liftU id α
liftU-id zero    = refl
liftU-id (suc α) = refl

renU-id (` x)           = refl
renU-id (ƛ t)         = cong
  ƛ
  (trans
    (renU-id t)
    (renU-cong liftU-id t)) 
renU-id (t · u)         = cong₂ _·_ (renU-id t) (renU-id u)

--

SubU : ℕ → ℕ → Set
SubU m n = Fin m → n ⊢

liftUs : ∀{m n} → SubU m n → SubU (suc m) (suc n)
liftUs ρ zero = ` zero
liftUs ρ (suc x) = renU suc (ρ x)

subU     : ∀{m n} → SubU m n → m ⊢ → n ⊢
subU σ (` x)          = σ x
subU σ (ƛ t)        = ƛ (subU (liftUs σ) t) 
subU σ (t · u)        = subU σ t · subU σ u

extendU : ∀{m n} → SubU m n → n ⊢ → SubU (suc m) n
extendU σ t zero    = t
extendU σ t (suc x) = σ x

liftsU-cong : ∀{m n}{σ σ' : SubU m n}
  → (∀ α → σ α ≡ σ' α)
  → (α : Fin (suc m))
  → liftUs σ α ≡ liftUs σ' α
liftsU-cong p zero    = refl
liftsU-cong p (suc α) = cong (renU suc) (p α) 

subU-cong : ∀{m n}{σ σ' : SubU m n}
  → (∀ α → σ α ≡ σ' α)
  → (t : m ⊢)
  → subU σ t ≡ subU σ' t
subU-cong p (` x)     = p x
subU-cong p (ƛ t)     = cong ƛ (subU-cong (liftsU-cong p) t)
subU-cong p (t · u)   = cong₂ _·_ (subU-cong p t) (subU-cong p u)

liftsU-id : ∀{n} → (α : Fin (suc n)) → ` α ≡ liftUs ` α
liftsU-id zero    = refl
liftsU-id (suc α) = refl

subU-id : ∀{n} → (t : n ⊢) → t ≡ subU ` t
subU-id (` x)           = refl
subU-id (ƛ t)           = cong ƛ (trans (subU-id t) (subU-cong liftsU-id t))
subU-id (t · u)         = cong₂ _·_ (subU-id t) (subU-id u)
\end{code}

\noindent To define the $\beta$-rule we need need to be able to
perform substitution on one variable only. As for syntaxes in earlier
sections we define parallel renaming and substitution first and get
substitution on one variable as a special case. We omit the details
here which are analogous to earlier sections.

\begin{code}
_[_]U : ∀{n} → suc n ⊢ → n ⊢ → n ⊢
\end{code}
\begin{code}[hide]
t [ u ]U = subU (extendU ` u) t
\end{code}
\begin{code}[hide]
backVar⋆ : ∀{Φ}(Γ : CtxNf Φ) → Fin (lenNf Γ) → Φ ⊢Nf⋆ *
backVar⋆ (Γ ,⋆ J) x = weakenNf⋆ (backVar⋆ Γ x)
backVar⋆ (Γ , A) zero    = A
backVar⋆ (Γ , A) (suc x) = backVar⋆ Γ x

backVar : ∀{Φ}(Γ : CtxNf Φ)(i : Fin (lenNf Γ)) → Γ ∋Nf (backVar⋆ Γ i)
backVar (Γ ,⋆ J) x      = T (backVar Γ x)
backVar (Γ , A) zero    = Z
backVar (Γ , A) (suc x) = S (backVar Γ x)

backVar⋆-eraseVar : ∀{Φ}{Γ : CtxNf Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋Nf A) →
  backVar⋆ Γ (eraseVarNf x) ≡ A
backVar⋆-eraseVar Z = refl
backVar⋆-eraseVar (S x) = backVar⋆-eraseVar x
backVar⋆-eraseVar (T x) = cong weakenNf⋆ (backVar⋆-eraseVar x)

conv∋-S : ∀{Φ}{Γ : CtxNf Φ}{B A A' : Φ ⊢Nf⋆ *}(p : A ≡ A')(x : Γ ∋Nf A) →
  conv∋Nf p (S {B = B} x) ≡ S (conv∋Nf p x)
conv∋-S refl x = refl

conv∋-T : ∀{Φ}{Γ : CtxNf Φ}{A A' : Φ ⊢Nf⋆ *}{K} →
  (p : A ≡ A')(q : weakenNf⋆ {K = K} A ≡ weakenNf⋆ A') → (x : Γ ∋Nf A) →
  conv∋Nf q (T x) ≡ T (conv∋Nf p x)
conv∋-T refl refl x = refl

cong-erase-ren : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(ρ⋆ : Ren⋆ Φ Ψ)
  → (ρ : RenNf Γ Δ ρ⋆){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋Nf A)(x' : Γ ∋Nf A') → conv∋Nf p x' ≡ x
  → eraseVarNf (ρ x) ≡ eraseVarNf (ρ x')
cong-erase-ren ρ⋆ ρ refl x .x refl = refl

backVar-eraseVar : ∀{Φ}{Γ : CtxNf Φ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋Nf A) →
  conv∋Nf (backVar⋆-eraseVar x) (backVar Γ (eraseVarNf x)) ≡ x
backVar-eraseVar Z = refl
backVar-eraseVar {Γ = Γ , A} (S x) = trans
  ((conv∋-S (backVar⋆-eraseVar x) (backVar _ (eraseVarNf x))))
  (cong S (backVar-eraseVar x))
backVar-eraseVar (T x) = trans
  (conv∋-T (backVar⋆-eraseVar x)
           (cong weakenNf⋆ (backVar⋆-eraseVar x))
           (backVar _ (eraseVarNf x)))
  (cong T (backVar-eraseVar x))


eraseVar-backVar : ∀{Φ}(Γ : CtxNf Φ)(x : Fin (lenNf Γ)) →
  eraseVarNf (backVar Γ x) ≡ x
eraseVar-backVar ∅        ()
eraseVar-backVar (Γ ,⋆ J) x      = eraseVar-backVar Γ x
eraseVar-backVar (Γ , A) zero    = refl
eraseVar-backVar (Γ , A) (suc x) = cong suc (eraseVar-backVar Γ x)

--

erase-Ren : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(ρ⋆ : Ren⋆ Φ Ψ)
  → RenNf Γ Δ ρ⋆ → RenU (lenNf Γ) (lenNf Δ) 
erase-Ren ρ⋆ ρ i = eraseVarNf (ρ (backVar _ i))

ext-erase : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(ρ⋆ : Ren⋆ Φ Ψ)
  → (ρ : RenNf Γ Δ ρ⋆){A : Φ ⊢Nf⋆ *}(α : Fin (lenNf (Γ , A)))
  → erase-Ren ρ⋆ (liftNf ρ {B = A}) α ≡ liftU (erase-Ren ρ⋆ ρ) α
ext-erase ρ⋆ ρ zero    = refl
ext-erase ρ⋆ ρ (suc α) = refl

conv∋-erase : ∀{Φ}{Γ : CtxNf Φ}{A A' : Φ ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (x : Γ ∋Nf A)
  → eraseVarNf (conv∋Nf p x) ≡ eraseVarNf x
conv∋-erase refl x = refl

conv⊢-erase : ∀{Φ}{Γ : CtxNf Φ}{A A' : Φ ⊢Nf⋆ *}
  → (p : A ≡ A')
  → (t : Γ ⊢Nf A)
  → eraseNf (conv⊢Nf p t) ≡ eraseNf t
conv⊢-erase refl t = refl

ext⋆-erase : ∀{Φ Ψ K}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(ρ⋆ : Ren⋆ Φ Ψ)
  → (ρ : RenNf Γ Δ ρ⋆)(α : Fin (lenNf Γ))
  → erase-Ren (lift⋆ ρ⋆ {K = K}) (⋆liftNf ρ) α ≡ erase-Ren ρ⋆ ρ α
ext⋆-erase {Γ = Γ} ρ⋆ ρ α = conv∋-erase
  (trans (sym (renNf⋆-comp (backVar⋆ Γ α))) (renNf⋆-comp (backVar⋆ Γ α)))
  (T (ρ (backVar Γ α))) 

ren-erase : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(ρ⋆ : Ren⋆ Φ Ψ)
  → (ρ : RenNf Γ Δ ρ⋆){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢Nf A)
  →  eraseNf (renNf ρ t) ≡ renU (erase-Ren ρ⋆ ρ) (eraseNf t)
ren-erase ρ⋆ ρ (` x) = cong `
 (cong-erase-ren
   ρ⋆
   ρ
   (backVar⋆-eraseVar x)
   x
   (backVar _ (eraseVarNf x))
   (backVar-eraseVar x))
ren-erase ρ⋆ ρ (ƛ t)            = cong ƛ
  (trans
    ((ren-erase ρ⋆ (liftNf ρ) t))
    (renU-cong (ext-erase ρ⋆ ρ) (eraseNf t)))
ren-erase ρ⋆ ρ (t · u)            =
  cong₂ _·_ (ren-erase ρ⋆ ρ t) (ren-erase ρ⋆ ρ u)
ren-erase ρ⋆ ρ (Λ t)            = trans
  (ren-erase (lift⋆ ρ⋆) (⋆liftNf ρ) t)
  (renU-cong (ext⋆-erase ρ⋆ ρ) (eraseNf t))
ren-erase ρ⋆ ρ (_·⋆_ {B = B} t A) = trans
  ((conv⊢-erase (sym (ren[]Nf⋆ ρ⋆ B A)) (renNf ρ t ·⋆ renNf⋆ ρ⋆ A)))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (wrap A t) = trans
  (conv⊢-erase (ren[]Nf⋆ ρ⋆ A (μ A)) (renNf ρ t))
  (ren-erase ρ⋆ ρ t)
ren-erase ρ⋆ ρ (unwrap {A = A} t) = trans
  (conv⊢-erase (sym (ren[]Nf⋆ ρ⋆ A (μ A))) (unwrap (renNf ρ t)))
  (ren-erase ρ⋆ ρ t)

--
erase-Sub : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(σ⋆ : SubNf⋆ Φ Ψ)
  → SubNf Γ Δ σ⋆ → SubU (lenNf Γ) (lenNf Δ) 
erase-Sub σ⋆ σ i = eraseNf (σ (backVar _ i))

cong-erase-sub : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(σ⋆ : SubNf⋆ Φ Ψ)
  → (σ : SubNf Γ Δ σ⋆){A A' : Φ ⊢Nf⋆ *}(p : A' ≡ A)
  → (x : Γ ∋Nf A)(x' : Γ ∋Nf A') → conv∋Nf p x' ≡ x
  → eraseNf (σ x) ≡ eraseNf (σ x')
cong-erase-sub σ⋆ σ refl x .x refl = refl

exts-erase : ∀ {Φ Ψ}{Γ Δ}(σ⋆ : SubNf⋆ Φ Ψ)(σ : SubNf Γ Δ σ⋆)
  → {B : Φ ⊢Nf⋆ *}
  → (α : Fin (suc (lenNf Γ)))
  → erase-Sub σ⋆ (liftsNf σ⋆ σ {B}) α ≡ liftUs (erase-Sub σ⋆ σ) α
exts-erase σ⋆ σ zero = refl
exts-erase {Γ = Γ}{Δ} σ⋆ σ {B} (suc α) = trans
  (conv⊢-erase
    (renNf⋆-id (subNf⋆ σ⋆ (backVar⋆ Γ α)))
    (renNf (conv∋Nf (sym (renNf⋆-id _)) ∘ S) (σ (backVar Γ α))) )
  (trans (ren-erase id (conv∋Nf (sym (renNf⋆-id _)) ∘ S) (σ (backVar Γ α)))
           (renU-cong (λ β → trans
             (conv∋-erase (sym (renNf⋆-id _)) (S (backVar Δ β)))
             (cong suc (eraseVar-backVar Δ β)))
             (eraseNf (σ (backVar Γ α)))))

exts⋆-erase : ∀ {Φ Ψ}{Γ Δ}(σ⋆ : SubNf⋆ Φ Ψ)(σ : SubNf Γ Δ σ⋆)
  → {B : Φ ⊢Nf⋆ *}
  → ∀{K}
  → (α : Fin (lenNf Γ))
  →  erase-Sub (liftsNf⋆ σ⋆ {K}) ( ⋆liftsNf σ⋆ σ) α ≡ erase-Sub σ⋆ σ α 
exts⋆-erase {Γ = Γ}{Δ} σ⋆ σ {B} α = trans
  (conv⊢-erase
    (weakenNf⋆-subNf⋆ σ⋆ (backVar⋆ Γ α))
    ((⋆weakenNf (σ (backVar Γ α))))) -- 
  (trans
    (ren-erase S T (σ (backVar Γ α)))
    (trans
      (renU-cong (eraseVar-backVar Δ) (eraseNf (σ (backVar Γ α))))
      (sym (renU-id (eraseNf (σ (backVar Γ α)))))))

sub-erase : ∀{Φ Ψ}{Γ : CtxNf Φ}{Δ : CtxNf Ψ}(σ⋆ : SubNf⋆ Φ Ψ)
  → (σ : SubNf Γ Δ σ⋆){A : Φ ⊢Nf⋆ *} → (t : Γ ⊢Nf A)
  →  eraseNf (subNf σ⋆ σ t) ≡ subU (erase-Sub σ⋆ σ) (eraseNf t) 
sub-erase σ⋆ σ (` x) =
  cong-erase-sub
    σ⋆
    σ
    (backVar⋆-eraseVar x)
    x
    (backVar _ (eraseVarNf x))
    (backVar-eraseVar x)
sub-erase σ⋆ σ (ƛ t) = cong ƛ
  (trans ((sub-erase σ⋆ (liftsNf σ⋆ σ) t))
         (subU-cong (exts-erase σ⋆ σ) (eraseNf t)))
sub-erase σ⋆ σ (t · u) = cong₂ _·_ (sub-erase σ⋆ σ t) (sub-erase σ⋆ σ u)
sub-erase σ⋆ σ (Λ {B = B} t) = trans
  ((conv⊢-erase (subNf⋆-liftNf⋆ σ⋆ B) (subNf (liftsNf⋆ σ⋆) (⋆liftsNf σ⋆ σ) t)))
  (trans (sub-erase (liftsNf⋆ σ⋆) (⋆liftsNf σ⋆ σ) t)
         (subU-cong (exts⋆-erase σ⋆ σ {B = Π B}) (eraseNf t)))
sub-erase σ⋆ σ (_·⋆_ {B = B} t A) = trans
  ((conv⊢-erase (sym (subNf⋆-[]Nf⋆ σ⋆ A B)) (subNf σ⋆ σ t ·⋆ subNf⋆ σ⋆ A)))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (wrap A t) = trans
  (conv⊢-erase (subNf⋆-[]Nf⋆ σ⋆ (μ A) A) (subNf σ⋆ σ t))
  (sub-erase σ⋆ σ t)
sub-erase σ⋆ σ (unwrap {A = A} t) = trans
  (conv⊢-erase (sym (subNf⋆-[]Nf⋆ σ⋆ (μ A) A)) (unwrap (subNf σ⋆ σ t)))
  (sub-erase σ⋆ σ t)
\end{code}

\noindent When erasing reduction steps below we will require two
properties about pushing erasure through a normalising single variable
substitution. These properties follow from properties of parallel
renaming and substitution:

\begin{code}
eraseNf-⋆[]Nf : ∀{Φ}{Γ : CtxNf Φ}{K B}(L : Γ ,⋆ K ⊢Nf B)(A : Φ ⊢Nf⋆ K)
  → eraseNf L ≡ eraseNf (L ⋆[ A ]Nf)
eraseNf-[]Nf : ∀{Φ}{Γ : CtxNf Φ}{A B}(L : Γ , A ⊢Nf B)(M : Γ ⊢Nf A)
  → eraseNf L [ eraseNf M ]U ≡ eraseNf (L [ M ]Nf)
\end{code}

\begin{code}[hide]
eraseNf-⋆[]Nf {Γ = Γ} N A = trans
  (trans
    (subU-id (eraseNf N))
    (subU-cong
      (λ α → trans
        (cong ` (sym (eraseVar-backVar Γ α)))
        ((sym (conv⊢-erase (weakenNf⋆[] _ _) (` (backVar Γ α))))))
      (eraseNf N)))
  (sym (sub-erase (extendNf⋆ (ne ∘ `) A) lem N))

eraseNf-[]Nf {Γ = Γ}{A = A}{B} N W = trans
  (trans
    (subU-cong
      (λ{ zero    → sym (conv⊢-erase (sym (subNf⋆-id A)) W)
        ; (suc α) → trans
               (cong ` (sym (eraseVar-backVar Γ α)))
               (sym (conv⊢-erase
                 (sym (subNf⋆-id (backVar⋆ Γ α)))
                 (` (backVar Γ α))))})
      (eraseNf N))
    ((sym (sub-erase
      (ne ∘ `)
      (extendNf
        (ne ∘ `)
        (conv⊢Nf (sym (subNf⋆-id _)) ∘ `)
        (conv⊢Nf (sym (subNf⋆-id A)) W))
      N))))
  (sym
    (conv⊢-erase
      (subNf⋆-id B)
      ( subNf (ne ∘ `)
         (extendNf
           (ne ∘ `)
           (conv⊢Nf (sym (subNf⋆-id _)) ∘ `)
           (conv⊢Nf (sym (subNf⋆-id A)) W))
         N )))
\end{code}

\noindent There is only one value in untyped lambda calculus: lambda.

\begin{code}
data UValue {n} : n ⊢ → Set where
  V-ƛ : (t : suc n ⊢) → UValue (ƛ t)
\end{code}

\noindent We define a call-by-value small-step reduction relation that
is intrinsically scoped.

\begin{code}
data _U—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L U—→ L' → L · M U—→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → UValue L → M U—→ M' → L · M U—→ L · M'
  β-ƛ  : {L : suc n ⊢}{M : n ⊢} → UValue M → ƛ L · M U—→ L [ M ]U
\end{code}

\noindent Erasing values is straightforward. The only tricky part is
to ensure that in values the subterms of the values for wrap and Λ are
also values as discussed earlier. This ensures that after when we
erase a typed value we will always get an untyped value:

\begin{code}
eraseVal : ∀{Φ A}{Γ : CtxNf Φ}{t : Γ ⊢Nf A} → Value t → UValue (eraseNf t)
eraseVal (V-ƛ t)    = V-ƛ (eraseNf t)
eraseVal (V-Λ v)    = eraseVal v
eraseVal (V-wrap v) = eraseVal v
\end{code}

\noindent Erasing a reduction step is more subtle as we may either get
a typed reduction step (e.g., \AgdaInductiveConstructor{β-ƛ}) or the
step may disappear (e.g., \AgdaInductiveConstructor{β-wrap}). In the
latter case the erasure of the terms before and after reduction will
be identical:

\begin{code}
erase—→ : ∀{Φ A}{Γ : CtxNf Φ}{t t' : Γ ⊢Nf A}
  → t —→ t' → eraseNf t U—→ eraseNf t' ⊎ eraseNf t ≡ eraseNf t'
\end{code}

\noindent In the congruence cases for application what we need to do
depends on the result of erasing the underlying reduction step. We
make use of \AgdaFunction{map} for Sum types for this purpose, the
first argument explains what to do if the underlying step corresponds
to a untyped reduction step (we create an untyped congruence reducing
step) and the second argument explains what to do if the underlying
step disappears (we create an equality proof):

\begin{code}
erase—→ (ξ-·₁ {M = M} p)            =
  Sum.map ξ-·₁ (cong (_· eraseNf M)) (erase—→ p)
erase—→ (ξ-·₂ {V = V} p q)          =
  Sum.map (ξ-·₂ (eraseVal p)) (cong (eraseNf V ·_)) (erase—→ q)
\end{code}

\noindent In the following cases the outer reduction step is removed:

\begin{code}
erase—→ (ξ-·⋆ p)      = erase—→ p
erase—→ (ξ-Λ p)       = erase—→ p
erase—→ (ξ-unwrap p)  = erase—→ p
erase—→ (ξ-wrap p)    = erase—→ p
\end{code}

\noindent In the case of β-reduction for an ordinary application we
always produce a corresponding untyped β-reduction step:

\begin{code}
erase—→ (β-ƛ {L = L}{M = M} V)      = inl (subst
  (ƛ (eraseNf L) · eraseNf M U—→_)
  (eraseNf-[]Nf L M)
  (_U—→_.β-ƛ {L = eraseNf L}{M = eraseNf M} (eraseVal V)))
\end{code}

\noindent In the other two β-reduction cases the step is always
removed, e.g., \AgdaInductiveConstructor{unwrap}
(\AgdaInductiveConstructor{wrap} \AgdaBound{A} \AgdaBound{L})
\AgdaDatatype{—→} \AgdaBound{L} becomes \AgdaBound{L} \AgdaDatatype{≡}
\AgdaBound{L}:

\begin{code}
erase—→ (β-Λ  {L = L}{A = A} V)     = inr (eraseNf-⋆[]Nf L A)
erase—→ (β-wrap _)                  = inr refl
\end{code}

\noindent That concludes the proof: either a typed reduction step
corresponds to an untyped one or no step at all.

We can combine erasure of values and reduction steps to get a progress
like result for untyped terms via erasure. Via typed progress we
either arrive immediately at an untyped value, or a typed reduction
step must exist and it will corr respond to an untyped step, or the
step disappears:

\begin{code}
erase-progress∅ : ∀{A : ∅ ⊢Nf⋆ *}(L : ∅ ⊢Nf A)
   → UValue (eraseNf L)
   ⊎ Σ (∅ ⊢Nf A) λ L' → (L —→ L')
     × (eraseNf L U—→ eraseNf L' ⊎ eraseNf L ≡ eraseNf L')
erase-progress∅ L =
  Sum.map eraseVal (λ {(L' ,, p) → L' ,, p ,, (erase—→ p)}) (progress∅ L)
\end{code}

\section{Execution}
\label{sec:execution}
\begin{code}[hide]
open import Data.Nat
open import Data.Maybe as Maybe
\end{code}

We can iterate progress an arbitrary number of times to run
programs. First, we define the reflexive transitive closure of
reduction. We will use this to represent traces of execution:

\begin{code}
data _—→*_ {Φ Γ} : {A : Φ ⊢Nf⋆ *} → Γ ⊢Nf A → Γ ⊢Nf A → Set where
  refl—→  : ∀{A}{M : Γ ⊢Nf A} → M —→* M
  trans—→ : ∀{A}{M  M' M'' : Γ ⊢Nf A}
    → M —→ M' → M' —→* M'' → M —→* M''
\end{code}

\noindent The \AgdaFunction{run} function takes a number of allowed
steps and a term. It returns another term, a proof that the original
term reduces to the new term in zero or more steps and possibly a
proof that the new term is a value. If no value proof is returned this
indicates that we did not reach a value in the allowed number of
steps.

If we are allowed zero more steps we return failure immediately. If we
are allowed more steps then we call progress to make one. If we get a
value back we return straight away with a value. If we have not yet
reached a value we call \AgdaFunction{run} recursively having spent a
step. We then prepend our step to the sequence of steps returned by
run and return:

\begin{code}
run : ∀ {A : ∅ ⊢Nf⋆ *} → ℕ → (M : ∅ ⊢Nf A)
  → Σ (∅ ⊢Nf A) λ M' → (M —→* M') × Maybe (Value M')
run zero M = M ,, refl—→ ,, nothing
run (suc n) M with progress∅ M
run (suc n) M | inl V = M ,, refl—→ ,, just V
run (suc n) M | inr (M' ,, p) with run n M'
... | M'' ,, q ,, mV = M'' ,, trans—→ p q ,, mV
\end{code}

\subsection{Erasure}

Given that the evaluator \AgdaFunction{run} produces a trace of
reduction that (if it doesn't run out of allowed steps) leads to a
value we can erase the trace and value to yield a trace of untyped
execution leading to an untyped value. Note that the untyped trace may
be shorter as some steps may disappear.

We define the the reflexive transitive closure of untyped reduction
analogously to the typed version:

\begin{code}
data _U—→*_ {n} : n ⊢ → n ⊢ → Set where
  reflU—→   : {M : n ⊢} → M U—→* M
  transU—→  : {M  M' M'' : n ⊢}
    → M U—→ M' → M' U—→* M'' → M U—→* M''
\end{code}

\noindent We can erase a typed trace to yield an untyped trace. The
reflexive case is straightforwards. In the transitive case, we may
have a step \AgdaBound{p} that corresponds to an untyped or it may
disappear. We use case \AgdaFunction{[\_,\_]} instead of
\AgdaFunction{map} this time. It is like \AgdaFunction{map} but
instead of producing another sum it (in the non-dependent case that we
are in) produces a result of an the same type in each case (in our
case \AgdaFunction{erase} \AgdaBound{M} \AgdaDatatype{—→}
\AgdaFunction{erase} \AgdaBound{M''}). In the first case we get an
untyped \AgdaBound{step} and rest of the trace is handled by the
recursive call. In the second case \AgdaBound{eq} is an equation
\AgdaFunction{erase} \AgdaBound{M} \AgdaDatatype{≡}
\AgdaFunction{erase} \AgdaBound{M'} which we use to coerce the
recursive call of type \AgdaFunction{erase} \AgdaBound{M'}
\AgdaDatatype{—→} \AgdaFunction{erase} \AgdaBound{M''} into type
\AgdaFunction{erase} \AgdaBound{M} \AgdaDatatype{—→}
\AgdaFunction{erase} \AgdaBound{M''} and the length of the trace is
reduced:

\begin{code}
erase—→* : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : CtxNf Φ}{t t' : Γ ⊢Nf A}
  → t —→* t' → eraseNf t U—→* eraseNf t'
erase—→* refl—→ = reflU—→
erase—→* (trans—→ {M'' = M''} p q) =
  [ (λ step → transU—→ step (erase—→* q))
  , (λ eq → subst (_U—→* eraseNf M'') (sym eq) (erase—→* q))
  ] (erase—→ p)
\end{code}

\noindent Finally we can use \AgdaFunction{run} to get an untyped
trace leading to a value, allowed steps permitting.

\begin{code}
erase-run : ∀ {A : ∅ ⊢Nf⋆ *} → ℕ → (M : ∅ ⊢Nf A)
  → Σ (0 ⊢) λ M' → (eraseNf M U—→* M') × Maybe (UValue M')
erase-run n M with run n  M
... | M' ,, p ,, mv = eraseNf M' ,, erase—→* p ,, Maybe.map eraseVal mv
\end{code}


\section{Examples}
\label{sec:examples}

Using only the facilities of System $F$ without the extensions of type
functions and recursive types we can define natural numbers as Church
Numerals:
\begin{code}
ℕᶜ : ∀{Φ} → Φ ⊢Nf⋆ *
ℕᶜ = Π ((ne (` Z)) ⇒ (ne (` Z) ⇒ ne (` Z)) ⇒ (ne (` Z)))

Zeroᶜ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf ℕᶜ
Zeroᶜ = Λ (ƛ (ƛ (` (S Z))))

Succᶜ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf ℕᶜ ⇒ ℕᶜ
Succᶜ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (ne (` Z)) · (` (S Z)) · (` Z))))))

Twoᶜ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf ℕᶜ
Twoᶜ = Succᶜ · (Succᶜ · Zeroᶜ)

Fourᶜ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf ℕᶜ
Fourᶜ = Succᶜ · (Succᶜ · (Succᶜ · (Succᶜ · Zeroᶜ)))

TwoPlusTwoᶜ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf ℕᶜ
TwoPlusTwoᶜ = Twoᶜ ·⋆ ℕᶜ · Twoᶜ · Succᶜ
\end{code}

\noindent Using the full facilities of System $F_{\omega\mu}$ we can
define natural numbers as Scott Numerals \cite{plotkin}. We the $Z$
combinator instead of the $Y$ combinator as it works for both lazy and
strict languages.

\begin{code}
G : ∀{Φ} → Φ ,⋆  * ⊢Nf⋆ *
G = Π (ne (` Z) ⇒ (ne (` (S Z)) ⇒ ne (` Z)) ⇒ ne (` Z))

M : ∀{Φ} → Φ ⊢Nf⋆ *
M = μ G

N : ∀{Φ} → Φ ⊢Nf⋆ *
N  =  G [ M ]Nf⋆

Zero : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N
Zero = Λ (ƛ (ƛ (` (S (Z )))))

Succ : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ (` Z · wrap _ (` (S (S (T Z))))))))

Two : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N
Two = Succ · (Succ · Zero)

Four : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N
Four = Succ · (Succ · (Succ · (Succ · Zero)))

case : ∀{Φ}{Γ : CtxNf Φ}
  → Γ ⊢Nf N ⇒ (Π (ne (` Z) ⇒ (N ⇒ ne (` Z)) ⇒ ne (` Z)))
case = ƛ (Λ (ƛ (ƛ (
 (` (S (S (T Z)))) ·⋆ ne (` Z) · (` (S Z)) · (ƛ (` (S Z) · unwrap (` Z)))))))

Z-comb : ∀{Φ}{Γ : CtxNf Φ} →
  Γ ⊢Nf Π (Π (((ne (` (S Z)) ⇒ ne (` Z)) ⇒ ne (` (S Z)) ⇒ ne (` Z))
    ⇒ ne (` (S Z)) ⇒ ne (` Z)))
Z-comb = Λ (Λ (ƛ (ƛ (` (S Z) · ƛ (unwrap (` (S Z)) · ` (S Z) · ` Z))
  · wrap (ne (` Z) ⇒ ne (` (S (S Z))) ⇒ ne (` (S Z)))
         (ƛ (` (S Z) · ƛ (unwrap (` (S Z)) · ` (S Z) · ` Z))))))

Plus : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N ⇒ N ⇒ N
Plus = ƛ (ƛ ((Z-comb ·⋆ N) ·⋆ N · (ƛ (ƛ ((((case · ` Z) ·⋆ N)
  · ` (S (S (S Z)))) · (ƛ (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

TwoPlusTwo : ∀{Φ}{Γ : CtxNf Φ} → Γ ⊢Nf N
TwoPlusTwo = (Plus · Two) · Two
\end{code}

\section{Scaling up from System $F_{\omega\mu}$ to Plutus Core}
\label{sec:real-world}

This formalisation forms the basis of a formalisation of Plutus
Core. There are two key extensions.

\subsection{Higher kinded recursive types}

In this paper we used $\mu : (* \rightarrow *) \rightarrow *$. This is
easy to understand and makes it possible to express simple examples
directly.  This corresponds to the version of recursive types one
might use in ordinary System $F$. In System $F_\omega$ we have a
greater degree of freedom. We have settled on an indexed version of
$\mu : ((k \rightarrow *) \rightarrow k \rightarrow *) \rightarrow k
\rightarrow *$ that supports the encoding of mutually defined
datatypes. This extension is straightforward in iso-recursive types,
in equi-recursive it is not.  We chose to present the restricted
version in this paper as it is simpler and sufficient to present our
examples. See the accompanying paper \cite{compilation} for a more
detailed discussion of higher kinded recursive types.

\subsection{Integers, bytestrings and cryptographic operations}

In Plutus Core we also extend System $F_{\omega\mu}$ with integers and
bytestrings and some cryptographic operations such as checking
signatures. Before thinking about how to add these features to our
language, there is a choice to be made when modelling integers and
bytestrings and cryptographic operations in Agda about whether we
consider them internal or external to our model. We are modelling the
Haskell implementation of Plutus Core which uses the Haskell
bytestring library. We chose to model the Plutus Core implementation
alone and consider bytestrings as an external black box. We assume
(i.e. postulate in Agda) an interface given as a type for bytestrings
and various operations such as take, drop, append etc. We can also
make clear our expectations of this interface by assuming
(postulating) some properties such as that append is
associative. Using pragmas in Agda we can ensure that when we compile
our Agda program to Haskell these opaque bytestring operations are
compiled to the real operations of the Haskell bytestring library. We
have taken a slightly different approach with integers as Agda and
Haskell have native support for integers and Agda integers are already
compiled to Haskell integers by default so we just make use of this
builtin support. Arguably this brings integers inside our model. One
could also treat integers as a blackbox. We treat cryptographic
operations as a blackbox as we do with bytestrings.

To add integers and bytestrings to the System $F_{\omega\mu}$ we add
type constants as types and term constants as terms. The type of a
term constant is a type constant. This ensures that we can have term
variables whose type is type constant but not term constants whose
type is a type variable. To support the operations for integers and
bytestrings we add a builtin constructor to the term language,
signatures for each operation, and a semantics for builtins that
applies the appropriate underlying function to its arguments. The
underlying function is postulated in Agda and when compiled to Haskell
it runs the appropriate native Haskell function or library
function. Note that the cryptographic functions are operations on
bytestrings.

Adding this functionality did not pose any particular formalisation
challenges except for the fact it was quite a lot of work. However,
compiling our implementation of builtins to Haskell did trigger
several bugs in Agda's GHC backend which were rapidly diagnosed and
fixed by the Agda developers.

\subsection{Using our implementation for testing}

As we can compile our Agda Plutus Core interpreter to Haskell we can
test the production Haskell Plutus Core interpreter against it. We
make use of the production system's parser and pretty printer which we
import as a Haskell library and use the same libraries for bytestrings
and cryptographic functions. The parser produces intrinsically typed
terms which we scope check and convert to a representation with de
Bruijn indices. We cannot currently use the intrinsically typed
implementation we describe in this paper directly as we must type
check terms first and formalising a type checker is future
work. Instead we have implemented a separate extrinsically typed
version that we use for testing. After evaluation we convert the de
Bruijn syntax back to a named syntax and pretty print the output.  We
have proven that for any well-typed term the intrinsic and extrinsic
versions give the same results after erasure.

\section*{Acknowledgements}

We thank the anonymous reviewers for their helpful comments and
insightful constructive criticism. We thank IOHK for their support of
this work. We thank our colleagues Marko Dimjašević, Kenneth
MacKenzie, and Michael Peyton Jones for helpful comments on an
multiple drafts. The first author would like to James McKinna for
spending an afternoon explaining pure type systems and Guillaume
Allais, Apostolis Xekoukoulotakis and Ulf Norell for help with
diagnosing and fixing bugs that we encountered in Agda's GHC backend
in the course of writing this paper.

%functional programs on a blockchain. In addition to the features
%presented here Plutus Core also has intrinsically sized integer and
%bytestrings and a more liberal version of recursive types.
%
%The extension to intrinsically sized integers and bytestrings requires
%quite a bit of infrastructure but the liberalisation of recursive
%types is almost trivial in this setting.
%
\bibliography{bibliography}
\end{document}

Some additional proofs added after publication and not shown in the paper

\begin{code}
open import Relation.Nullary

-- a value can make no progress

val : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢Nf σ} → Value t → ¬ (Σ (Γ ⊢Nf σ) (t —→_))
val (V-ƛ p)    ()
val (V-Λ p)    (.(Λ _) ,, ξ-Λ q)         = val p (_ ,, q)
val (V-wrap p) (.(wrap _ _) ,, ξ-wrap q) = val p (_ ,, q)

-- exclusive or
_xor_ : Set → Set → Set
A xor B = (A ⊎ B) × ¬ (A × B)

-- progress can be upgraded to an xor using val

progress-xor : {σ : ∅ ⊢Nf⋆ *}(t : ∅ ⊢Nf σ) → Value t xor Σ (∅ ⊢Nf σ) (t —→_)
progress-xor t = progress  _ t ,, λ{(v ,, p) → val v p}

-- The reduction rules are deterministic

det : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t t' t'' : Γ ⊢Nf σ}
  → (p : t —→ t')(q : t —→ t'') → t' ≡ t''
det (ξ-·₁ p)     (ξ-·₁ q)     = cong (_· _) (det p q)
det (ξ-·₁ p)     (ξ-·₂ w q)   = ⊥-elim (val w (_ ,, p))
det (ξ-·₂ v p)   (ξ-·₁ q)     = ⊥-elim (val v (_ ,, q))
det (ξ-·₂ v p)   (ξ-·₂ w q)   = cong (_ ·_) (det p q)
det (ξ-·₂ v p)   (β-ƛ w)      = ⊥-elim (val w (_ ,, p))
det (ξ-·⋆ p)     (ξ-·⋆ q)     = cong (_·⋆ _) (det p q)
det (β-Λ v)      (ξ-·⋆ q)     = ⊥-elim (val (V-Λ v) (_ ,, q))
det (ξ-·⋆ p)     (β-Λ v)      = ⊥-elim (val (V-Λ v) (_ ,, p))
det (ξ-Λ p)      (ξ-Λ q)      = cong Λ (det p q)
det (β-ƛ v)      (ξ-·₂ w q)   = ⊥-elim (val v (_ ,, q))
det (β-ƛ v)      (β-ƛ w)      = refl
det (β-Λ v)      (β-Λ w)      = refl
det (β-wrap p)   (β-wrap q)   = refl
det (β-wrap p)   (ξ-unwrap q) = ⊥-elim (val (V-wrap p) (_ ,, q))
det (ξ-unwrap p) (β-wrap q)   = ⊥-elim (val (V-wrap q) (_ ,, p))
det (ξ-unwrap p) (ξ-unwrap q) = cong unwrap (det p q)
det (ξ-wrap p)   (ξ-wrap q)   = cong (wrap _) (det p q)

-- Untyped values cannot make progress
valU : ∀{n}{t : n ⊢} → UValue t → ¬ (Σ (n ⊢) (t U—→_))
valU (V-ƛ t) ()

-- The untyped reduction rules are deterministic
detU : ∀{n}{t t' t'' : n ⊢}
  → (p : t U—→ t')(q : t U—→ t'') → t' ≡ t''
detU (ξ-·₁ p)   (ξ-·₁ q)   = cong (_· _) (detU p q)
detU (ξ-·₁ p)   (ξ-·₂ w q) = ⊥-elim (valU w (_ ,, p))
detU (ξ-·₂ v p) (ξ-·₁ q)   = ⊥-elim (valU v (_ ,, q))
detU (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (detU p q)
detU (ξ-·₂ v p) (β-ƛ w)    = ⊥-elim (valU w (_ ,, p))
detU (β-ƛ v)    (ξ-·₂ w q) = ⊥-elim (valU v (_ ,, q))
detU (β-ƛ v)    (β-ƛ w)    = refl
\end{code}
