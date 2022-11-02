\subsection{Recursive term bindings}
\label{sec:recursive-terms}

\begin{code}[hide]
{-# OPTIONS --type-in-type         #-}
{-# OPTIONS --no-termination-check #-}
module RecursiveTerms where
  open import IFix
  open import Common
\end{code}

\subsubsection{Self-reference and standard combinators.}

It is well-known that we cannot encode the Y combinator in the polymorphic
  lambda calculus, but that we \emph{can} encode it if we have recursive types \cite[Section 20.3]{Harper:PFPL}.\footnote{We here mean
\emph{arbitrary} recursive types, not merely strictly positive types. We cannot encode the Y
combinator in Agda, for example, without disabling the positivity check.} We need the
following types:

\begin{code}
  Fix₀ : (∗ → ∗) → ∗
  Fix₀ = IFix (λ Rec F → F (Rec F))

  -- Type for values which can be applied to themselves
  Self : ∗ → ∗
  Self a = Fix₀ (λ Rec → Rec → a)

  self : ∀ {A} → (Self A → A) → Self A
  self f = wrap f

  unself : ∀ {A} → Self A → Self A → A
  unself s = unwrap s

  selfApply : ∀ {A} → Self A → A
  selfApply s = unself s s
\end{code}

\noindent The first thing we defined was $\Fix0 : (\Type \kindArrow \Type)
\kindArrow \Type$, which is a fixpoint operator that only works at kind $\Type$.
We won't need the full power of $\ifix$ for this section, so the techniques
here should be applicable for other recursive variants of \FOM{}, provided
they are able to define $\Fix0$.

Now we can define the Y combinator and its $\eta$-expanded version, the Z combinator.

\begin{code}
  y : ∀ {A} → (A → A) → A
  y f = (λ z → f (selfApply z))
        (self (λ z → f (selfApply z)))

  z : ∀ {A B : ∗} → ((A → B) → (A → B)) → (A → B)
  z f = (λ z → f (λ a → (selfApply z) a))
        (self (λ z → f (λ a → (selfApply z) a)))
\end{code}

\noindent In strict lambda calculi the Y combinator does not terminate, and we need to use
the Z combinator, which has a more restricted type (it only allows us to take
the fixpoint of things of type $A \rightarrow B$).

\subsubsection{Mutual recursion.}

The Y and Z combinators allow us to define singly recursive functions, but we also
want to define \emph{mutually} recursive functions.

This is easy in a non-strict lambda calculus: we have the Y combinator, and we know
how to encode tuples, so we can simply define a recursive \emph{tuple} of
functions. However, this is still easy to get wrong, as we must be careful not
to force the recursive tuple too soon.

Moreover, this approach does not work with the Z combinator, since a tuple is not a function
(the Scott-encoded version is a function, but a \emph{polymorphic} function).

We can instead construct a more generic fixpoint combinator which will be usable in both
a non-strict and strict setting. We will present the steps
using recursive definitions for clarity, but all of these can be implemented
with the Z combinator.

Let us start with the function $\fix2$ which takes the fixpoint of a function
of 2-tuples.
\begin{code}
  fix₂ : ∀ {A B} → (A × B → A × B) → A × B
  fix₂ f = f (fix₂ f)
\end{code}

We can transform this as follows: first we curry $f$.
\begin{code}
  fix₂-uncurry : ∀ {A B} → (A → B → A × B) → A × B
  fix₂-uncurry f = (uncurry f) (fix₂-uncurry f)
\end{code}
Now, we replace both the remaining tuple types with Scott-encoded versions,
using the corresponding version of uncurry for Scott-encoded 2-tuples.
\begin{code}
  uncurry₂-scott
    : ∀ {A B R : ∗}
    → (A → B → R)
    → ((∀ {Q} → (A → B → Q) → Q) → R)
  uncurry₂-scott f g = g f

  fix₂-scott
    : ∀ {A B}
    → (A → B → ∀ {Q} → (A → B → Q) → Q)
    → ∀ {Q} → (A → B → Q) → Q
  fix₂-scott f = (uncurry₂-scott f) (fix₂-scott f)
\end{code}
Finally, we reorder the arguments to $f$ to make it look as regular as possible.
\begin{code}
  fix₂-rearrange
    : ∀ {A B}
    → (∀ {Q} → (A → B → Q) → A → B → Q)
    → ∀ {Q} → (A → B → Q) → Q
  fix₂-rearrange f k = (uncurry₂-scott (f k)) (fix₂-rearrange f)
\end{code}

\noindent This gives us a fixpoint function pairs of mutually recursive
values, but we want to handle \emph{arbitrary} sets of recursive values. At this
point, however, we notice that all we need to do to handle, say, triples, is to
replace $A \rightarrow B$ with $A \rightarrow B \rightarrow C$ and the binary
$\uncurry$ with the ternary $\uncurry$. And we can abstract over this pattern.

\begin{code}
  fixBy
    : ∀ {F : ∗ → ∗}
    → ((∀ {Q} → F Q → Q) → ∀ {Q} → F Q → Q)
    → (∀ {Q} → F Q → F Q) → ∀ {Q} → F Q → Q
  fixBy by f = by (fixBy by f) ∘ f
\end{code}

\noindent To get the behaviour we had before, we instantiate $\by$ appropriately:
\begin{code}
  by₂
    : ∀ {A B}
    → (∀ {Q} → (A → B → Q) → Q)
    → ∀ {Q} → (A → B → Q) → Q
  by₂ r k = (uncurry₂-scott k) r

  fixBy₂
    : ∀ {A B}
    → (∀ {Q} → (A → B → Q) → A → B → Q)
    → ∀ {Q} → (A → B → Q) → Q
  fixBy₂ = fixBy by₂
\end{code}

\noindent How do we interpret $\by$? Inlining $\mathsf{uncurry}$ into our definition of $\by_2$ we
find that it is in fact the identity function! However, by choosing the exact definition
we can tweak the termination
properties of our fixpoint combinator. Indeed, our current definition does not terminate
even in a non-strict language like Agda, since it evaluates the components of the recursive tuple
before feeding them into $f$. However, we can avoid this by ``repacking'' the tuple so that accessing one
of its components will no longer force the other.\footnote{We have defined × as a simple datatype,
rather than using the more sophisticated version in the Agda standard library. The standard library version has different
strictness properties \textemdash{} indeed, for that version $\texttt{repack}_2$ is precisely the identity.}

\begin{code}
  -- Repacking tuples.
  repack₂ : ∀ {A B} → A × B → A × B
  repack₂ tup = (proj₁ tup , proj₂ tup)

  -- Repacking Scott-encoded tuples.
  by₂-repack
    : ∀ {A B : ∗}
    → (∀ {Q : ∗} → (A → B → Q) → Q)
    → ∀ {Q : ∗} → (A → B → Q) → Q
  by₂-repack r k  = k (r (λ x y → x)) (r (λ x y → y))
\end{code}

\noindent Passing $\texttt{by}_2\texttt{-repack}$ to $\texttt{fixBy}$ gives us a fixpoint
combinator that terminates in a non-strict language like Agda or Haskell.

Can we write one that terminates in a strict language? We can, but we incur
the same restriction that we have when using the Z combinator: the recursive values must
all be functions. This is because we use exactly the same trick, namely $\eta$-expanding the values.

\begin{code}
  -- with tuples
  repack₂-strict
    : ∀ {A₁ B₁ A₂ B₂ : ∗}
    → (A₁ → B₁) × (A₂ → B₂)
    → (A₁ → B₁) × (A₂ → B₂)
  repack₂-strict tup = ((λ x → proj₁ tup x) , (λ x → proj₂ tup x))

  -- with Scott-encoded tuples
  by₂-strict
    : ∀ {A₁ B₁ A₂ B₂ : ∗}
    → (∀ {Q : ∗} → ((A₁ → B₁) → (A₂ → B₂) → Q) → Q)
    → ∀ {Q : ∗} → ((A₁ → B₁) → (A₂ → B₂) → Q) → Q
  by₂-strict r k = k (λ x → r (λ f₁ f₂ → f₁ x)) (λ x → r (λ f₁ f₂ → f₂ x))
\end{code}

\noindent This gives us general, $n$-ary fixpoint combinators in \FOMF{}.

\subsubsection{Formal encoding of recursive let-bindings.}

\input{RecursiveTermsFormal}

\subsubsection{Polymorphic recursion with the Z combinator.}

Neither the simple Z combinator nor our strict $\fixBy$ allow us to define recursive values
which are not of function type. This might not seem too onerous, but this also forbids defining
\emph{polymorphic} values, such as polymorphic functions. For example, we cannot
define a polymorphic map function this way.

Sometimes we can get around this problem by floating the type abstraction out of the recursion.
This will work in many cases, but fails in any instance of
polymorphic recursion, which includes most recursive functions over irregular datatypes.

However, we can work around this restriction if we are willing to transform our
program. The \emph{thunking} transformation is a variant of the well-known transformation
for simulating call-by-name evaluation in a call-by-value language \cite{danvy1992thunks}\cite{steele1976lambda}.
Conveniently, this also has the property that it transforms the ``thunked'' parameters into values
of \emph{function} type, thus making them computable with the Z combinator.

The thunking transformation takes a set of recursive definitions $f_i : T_i = b_i$ and transforms it by:
\begin{itemize}
  \item Defining the $\Unit$ datatype with a single, no-argument constructor $\Unitval$.
  \item Creating new (recursive) definitions $f_i' : \Unit \rightarrow T_i = \lambda (u : \Unit). b_i$.
  \item Replacing all uses of $f_i$ in the $b_i$s with $f_i'\ \Unitval$,
  \item Creating new (non-recursive) definitions $f_i : T_i = f_i'\ \Unitval$ to replace the originals.
\end{itemize}

\noindent Now our recursive value is truly of function type, rather
than universal type, so we can compile it as normal.

An example is given in \cref{fig:polyrec-example} of transforming a polymorphic map function.

\begin{figure}[!t]
  \centering
  \begin{displaymath}
  \begin{array}{l@{\ }l}
  \tlet\, \rec\, &map : \forall A\ B . (A \rightarrow B) \rightarrow (\List A \rightarrow \List B) = \\
  &\quad\Lambda A\ B .\ \lambda (f : A \rightarrow B)\ (l: \List A) \\
  &\quad\textsf{matchList}\, \{ A \}\ l\ \{\List B\}\\
  &\quad(\NNil\ \{B\})\\
  &\quad(\lambda (h : A) (t : \List A) . \CCons\ \{B\}\ (f\ h)\ (map\ \{A\}\ \{B\}\ f\ t))\\
  \tin\, t\\
  \\
  \Rightarrow\\
  \\
  \tlet\, \rec\, &map' : \Unit \rightarrow \forall A\ B . (A \rightarrow B) \rightarrow (\List A \rightarrow \List B) = \\
  &\quad\lambda (u : \Unit) .\ \Lambda A\ B .\ \lambda (f : A \rightarrow B)\ (l : \List A) \\
  &\quad\textsf{matchList}\ \{ A \}\ l\ \{\List B\}\\
  &\quad(\NNil\ \{B\})\\
  &\quad(\lambda (h : A) (t : \List A) . \CCons\ \{B\}\ (f\ h)\ (map'\ \Unitval\ \{A\}\ \{B\}\ f\ t))\\
  \tin\, \tlet\, &map : \forall A\ B . (A \rightarrow B) \rightarrow (\List A \rightarrow \List B) = map'\ \Unitval\\
  \tin\, t
  \end{array}
  \end{displaymath}

  \captionof{figure}{Example of transforming polymorphic recursion}
  \label{fig:polyrec-example}
\end{figure}
