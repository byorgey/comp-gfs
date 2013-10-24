% -*- mode: LaTeX; compile-command: "mk" -*-
\documentclass{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsmath}
\usepackage{brent}
\usepackage[all,cmtip]{xy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

\renewcommand{\False}{\cons{F}}
\renewcommand{\True}{\cons{T}}

\newcommand{\FinSet}{\ensuremath{\mathbf{FinSet}}}

\newcommand{\universe}{\ensuremath{\mathcal{U}}}
\newcommand{\defeq}{\mathrel{:\equiv}}
\newcommand{\dep}[1]{\prod_{#1}}
\newcommand{\fun}[1]{\lambda #1.\ }

\newcommand{\param}{\mathord{-}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title

\title{Computational Interpretation of Generating Functions via
  Indexed Semirings}
\author{Brent Yorgey}
\date{\today}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\maketitle

\section{Semirings}
\label{sec:intro}

For the purposes of this note, a \emph{semiring} $(S,+,0,\cdot,1)$ is
a type $S$ equipped with binary operations $+$ and $\cdot$ such that
$(S,+,0)$ is a commutative monoid, $(S,\cdot,1)$ is a monoid, $0 \cdot
a = a \cdot 0 = 0$, and $\cdot$ distributes over $+$.  As usual, we
will often abuse notation and denote a semiring simply by its carrier
type $S$ when the operations are clear from context.  We also
sometimes omit $\cdot$ and denote multiplication by juxtaposition, $a
\cdot b = ab$.

Examples of semirings (some of which will play an important role later)
include:
\begin{itemize}
\item Booleans under disjunction and conjunction, $(\B, \lor, \False,
  \land, \True)$.
\item Natural numbers under addition and multiplication,
  $(\N,+,0,\cdot,1)$.
\item Integers under addition and multiplication, $(\Z,+,0,\cdot,1)$.
\item The integers (or naturals), adjoined with $-\infty$, under
  maximum and addition, $(\Z \cup \{-\infty\},\max,-\infty,+,0)$.
\item Finite sets under disjoint union and cartesian product,
  $(\FinSet, \uplus, \varnothing, \times, \{\star\})$.  (Note
  that the laws hold only up to isomorphism of sets.)
\end{itemize}

By a semiring \emph{homomorphism} $\phi : S \to T$ we mean simply a
function $S \to T$ which preserves all the semiring structure, that
is, $\phi(0_S) = 0_T$, $\phi(1_S) = 1_T$, $\phi(a + b) = \phi(a) +
\phi(b)$, and $\phi(ab) = \phi(a)\phi(b)$.  Observe, for
example, that we have the sequence of semiring homomorphisms
\[
\xymatrix{
  (\FinSet, \uplus, \times, \varnothing, \{\star\})
  \ar[d]^{||\param||} \\
  (\N,+,\cdot,0,1)
  \ar[d]^{> 0} \\
  (\B, \lor, \land, \False, \True)
}
\]
going from a set $S$, to its size $||S||$, to its inhabitation $||S||>0$.

In connection with the theory of species, we typically consider formal
power series with coefficients taken from some numeric type like
natural numbers or integers.  However, as is well-known, given any
semiring $S$ we may form the semiring $S[[x]]$ of formal power series
with coefficients in $S$, with addition and multiplication of formal
power series defined in the usual way.  Note also that any semiring
homomorphism $\phi : S \to T$ induces a homomorphism over the
associated semirings of formal power series, which we notate as
$\phi[[x]] : S[[x]] \to T[[x]]$ (that is, $\param [[x]]$ is an endofunctor
on the category of semirings).

\section{Ordinary generating functions}
\label{sec:ogf}

Define OGFs. Homomorphism from species.  Note if we generalize OGFs
over arbitrary semirings, we can view the definition of an
(unlabelled) species itself as an OGF, and the homomorphism from
species to OGFs is revealed as the OGF homomorphism induced by the
underlying semiring homomorphism $||\param|| : (\FinSet, \uplus, \times,
\varnothing, \{\star\}) \to (\N,+,\cdot,0,1)$.  We then consider other
semiring homomorphisms to and from $\FinSet$, and discover we can
churn out algorithms to compute things about unlabelled species simply
by designing the proper semiring + homomorphism and transporting the
species-expression-as-OGF along the induced OGF homomorphism. (Many of
these algorithms are well-known and/or ``obvious''.) Exhibit some
Haskell code.

However, this only works for OGFs.  The idea is to generalize this
entire analysis from OGFs to EGFs and cycle index series, which
requires generalizing the notion of semiring.

\section{Indexed semirings}
\label{sec:indexed-semirings}

\emph{Indexed semirings} are a generalization of semirings where the
elements have types indexed by a natural number (their ``size'').  In
particular, an indexed semiring consists of
\begin{itemize}
\item A type family $S : \N \to \universe$ (where \universe\ denotes
  the universe of types). We use subscripts to denote applications of
  $S$, as in $S_n$.
\item A binary operation $\_ + \_ : \dep{n:\N} S_n \to S_n \to S_n$.
  We usually omit the size argument when it is clear from context.
\item A distinguished family of elements $0 : \dep{n:\N} S_n$.  We
  write $0_n$ when we wish to be explicit about the size, but usually
  omit it.
\item A binary operation $\_ \cdot \_ : \dep{m, n : \N} S_m \to S_n \to
  S_{m+n}$.  We usually omit the size arguments.
\item A distinguished element $1 : S_0$.
\end{itemize}
Moreover, these are subject laws analogous to the laws of a semiring:
\begin{itemize}
\item $\dep{n:\N} \dep{s : S_n} 0 + s = s + 0 = s$ \hfill ($0$ is an
  identity for $+$)
\item $\dep{n:\N} \dep{s, t, u : S_n} (s +
  t) + u = s + (t + u)$ \hfill (Associativity of $+$)
\item $\dep{n:\N} \dep{s, t : S_n} s + t = t + s$ \hfill
  (Commutativity of $+$)
\item $\dep{m, n:\N} \dep{s : S_n} 0_m \cdot s = s \cdot 0_m =
  0_{m+n}$ \hfill ($0$ is an annihilator for $\cdot$)
\item $\dep{n:\N} \dep{s : S_n} 1 \cdot s = s
  \cdot 1 = s$ \hfill ($1$ is an identity for $\cdot$)
\item $\dep {m, n, p: \N} \dep {s : S_m}
  \dep {t : S_n} \dep {u : S_p} (s \cdot t) \cdot u = s \cdot (t \cdot
  u)$ \hfill (Associativity of $\cdot$)
\item $\dep {m,n : \N} \dep {s : S_m} \dep{t,u : S_n} s \cdot (t + u)
  = s \cdot t + s \cdot u$ \hfill (Left distributivity)
\item $\dep {m,n : \N} \dep {s : S_m} \dep{t,u : S_n} (t + u) \cdot s
  = t \cdot s + u \cdot s$ \hfill (Right distributivity)
\end{itemize}

We can make any semiring $S$ into an indexed semiring $R$ by putting a
copy of $S$ at every size, that is, by defining $R_n \defeq S$, and
taking the binary operations of $R$ to be those of $S$, ignoring the
sizes.  In fact, we can see semirings as precisely those indexed
semirings where $+$, $\cdot$, and $0$ are defined uniformly over all
sizes.

For a more interesting example of an indexed semiring, consider the
following definition of the \term{binomial semiring}, $B$. We begin
with a copy of the natural numbers at each size, $B_n \defeq \N$, and
take the usual $0$, $1$, and $+$, defined uniformly for all sizes. For
the product operation, however, we define \[ \cdot_B = \fun {m, n :
  \N} \fun {a : B_m} \fun {b : B_n} \binom{m+n}{m} \cdot a \cdot b \]
where the product operations on the right-hand side are the usual
product of natural numbers.  For example, $4_2 \cdot_B 7_3 =
\binom{5}{2} 28 = 280$.  It is not hard to show that this satisfies
the indexed semiring laws.

\section{Exponential generating functions}
\label{sec:egfs}

Show how indexed semirings correspond to egfs (?)

\section{Generalized indexed semirings}
\label{sec:gen-indexed-semirings}

Index semirings over arbitrary monoids in place of $(\N,+,0)$.  Use
this to do the appropriate thing for cycle index series, indexed by
integer partitions (???)

The hope is that some non-obvious algorithms will ``fall out'' of
this, for e.g. enumerating unlabelled non-regular species.

\end{document}
