\subsection{Recursive datatype bindings}
\label{sec:recursive-data}

\begin{code}[hide]
{-# OPTIONS --type-in-type         #-}
module RecursiveData where
  open import IFix
  open import Common
  open import Agda.Builtin.Unit
\end{code}

Adding singly recursive types is comparatively straightforward. We can write our datatype
as a type-level function (often called a ``pattern functor'' \cite{backhouseetal98}) with a parameter for the
recursive use of the type, and then use our fixpoint operator to produce the final
datatype.\footnote{This is where the Scott encoding really departs from the Church encoding:
the recursive datatype itself appears in our encoding, since we are only doing a ``one-level''
fold whereas the Church encoding gives us a full recursive fold over the entire datastructure.}

\begin{code}
  ListF : (∗ → ∗) → (∗ → ∗)
  ListF List A =
    -- This is the normal Scott-encoding, using the
    -- recursive `List' provided by the pattern functor.
    ∀ {R : ∗} → R → (A → List A → R) → R

  List : ∗ → ∗
  List A = IFix ListF A
\end{code}

\noindent However, it is not immediately apparent how to use this to define \emph{mutually}
recursive datatypes. The type of $\ifix$ is quite restrictive: we can only produce
something of kind $k \kindArrow \Type$.

If we had kind-level products and an appropriate fixpoint operator, then we could do this
relatively easily by defining a singly recursive product of our datatypes. However,
we do not have products in our kind system.

But we can \emph{encode} type-level products. In \cite{fixmutualgeneric} the authors use
the fact that an $n$-tuple can be encoded as a function from an index to a value, and thus
type-level naturals can be used as the index of a type-level function to encode a tuple of types. We
take a similar approach except that we will not use a natural to index our type, but
rather a richer datatype. This will prove fruitful when encoding parameterized types.

Let's consider an example: the mutually recursive types of trees and forests.

\begin{code}
  mutual
    data Tree₀ (A : ∗) : ∗ where
      node₀ : A → Forest₀ A → Tree₀ A

    data Forest₀ (A : ∗) : ∗ where
      nil₀  : Forest₀ A
      cons₀ : Tree₀ A → Forest₀ A → Forest₀ A
\end{code}

\noindent First of all, we can rewrite this with a ``tag'' datatype indicating which of the two cases
in our datatype we want to use. That allows us to use a single data declaration to cover
both of the types. Moreover, the tag can include the type parameters of the datatype,
which is important in the case that they differ between the different datatypes.

\begin{code}
  data TreeForestᵗ : ∗ where
    -- `Treeᵗ A' tags the type `Tree A'
    Treeᵗ : ∗ → TreeForestᵗ
    -- `Forestᵗ A' tags the type `Forest A'
    Forestᵗ : ∗ → TreeForestᵗ

  module Single where
    -- This mutual recursion is not strictly necessary,
    -- and is only there so we can define the 'Tree'
    -- and `Forest' aliases for legibility.
    mutual
      -- Type alias for the application of the main
      -- datatype to the `Tree' tag
      Tree : ∗ → ∗
      Tree A = TreeForest (Treeᵗ A)

      -- Type alias for the application of the main
      -- datatype to the `Forest' tag
      Forest : ∗ → ∗
      Forest A = TreeForest (Forestᵗ A)

      data TreeForest : TreeForestᵗ → ∗ where
        node : ∀ {A} → A → Tree A → Tree A
        nil  : ∀ {A} → Forest A
        cons : ∀ {A} → Tree A → Forest A → Forest A
\end{code}

\noindent That has eliminated the mutual recursion, but we still have a number of problems:
\begin{itemize}
\item We are relying on Agda's data declarations to handle recursion, rather than
  our fixpoint combinator.
\item We are using inductive families, which we don't have a way to encode.
\item $\texttt{TreeForest}^t$ is being used at the kind level, but we don't have
  a way to encode datatypes at the kind level.
\end{itemize}

\noindent Fortunately, we can get past all of these problems. Firstly we need to make our handling
of the different constructors more uniform by encoding them as sums of
products.

\begin{code}
  module Constructors where
    mutual
      Tree : ∗ → ∗
      Tree A = TreeForest (Treeᵗ A)

      Forest : ∗ → ∗
      Forest A = TreeForest (Forestᵗ A)

      -- This chooses the type of the constructor
      -- given the tag
      TreeForestF : TreeForestᵗ → ∗
      -- The `Tree' constructor takes a pair of
      -- an `A' and a `Forest A'
      TreeForestF (Treeᵗ A)   = A × Forest A
      -- The `Forest' constructor takes either nothing,
      -- or a pair of a `Tree A' and a `Forest A'
      TreeForestF (Forestᵗ A) = ⊤ ⊎ Tree A × Forest A

      {-# NO_POSITIVITY_CHECK #-}
      data TreeForest (tag : TreeForestᵗ) : ∗ where
        treeForest : TreeForestF tag → TreeForest tag
\end{code}

\noindent If we now rewrite $\texttt{TreeForestF}$ to take the recursive type
as a parameter instead of using it directly, we can write this with $\ifix$.

\begin{code}
  module IFixed where
    TreeForestF : (TreeForestᵗ → ∗) → (TreeForestᵗ → ∗)
    TreeForestF Rec (Treeᵗ A)   = A × Rec (Forestᵗ A)
    TreeForestF Rec (Forestᵗ A) = ⊤ ⊎ Rec (Treeᵗ A) × Rec (Forestᵗ A)

    TreeForest : TreeForestᵗ → ∗
    TreeForest = IFix TreeForestF
\end{code}

\noindent Finally, we need to encode the remaining datatypes that we have used. The sums and products
in the right-hand-side of $\texttt{TreeForestF}$ should be Scott-encoded as usual, since
they represent the constructors of the datatype.

The tag type is more problematic. The Scott encoding of the tag type we have been using would be:
\begin{code}
  Scott-tag = ∀ {R : ∗} → (∗ → R) → (∗ → R) → R
\end{code}

\noindent However, we do not have polymorphism at the kind level! But if we look at how we use the tag we
see that we only ever match on it to produce something of kind $\Type$, and so we can get away
with immediately instantiating this to $\Type$.

\begin{code}
  module Encoded where
    -- Tag type instantiated to `∗'
    TreeForestᵉ : ∗
    TreeForestᵉ = (∗ → ∗) → (∗ → ∗) → ∗

    -- Encoded `Treeᵗ' tag
    Treeᵉ : ∗ → TreeForestᵉ
    Treeᵉ A = λ T F → T A

    -- Encoded `Forestᵗ' tag
    Forestᵉ : ∗ → TreeForestᵉ
    Forestᵉ A = λ T F → F A

    TreeForestF : (TreeForestᵉ → ∗) → (TreeForestᵉ → ∗)
    TreeForestF Rec tag =
      -- Pattern matching has been replaced by application
      tag
        -- The encoded `Tree' constructor
        (λ A → ∀ {R} → (A → Rec (Forestᵉ A) → R) → R)
        -- The encoded `Forest' constructor
        (λ A → ∀ {R} → R → (Rec (Treeᵉ A) → Rec (Forestᵉ A) → R) → R)

    TreeForest : TreeForestᵉ → ∗
    TreeForest = IFix TreeForestF
\end{code}

\noindent This, finally, gives us a completely \FOMF{}-compatible encoding of our mutually recursive datatypes.
