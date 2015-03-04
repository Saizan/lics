%-----------------------------------------------------------------------------
%
%               Template for sigplanconf LaTeX Class
%
% Name:         sigplanconf-template.tex
%
% Purpose:      A template for sigplanconf.cls, which is a LaTeX 2e class
%               file for SIGPLAN conference proceedings.
%
% Guide:        Refer to "Author's Guide to the ACM SIGPLAN Class,"
%               sigplanconf-guide.pdf
%
% Author:       Paul C. Anagnostopoulos
%               Windfall Software
%               978 371-2316
%               paul@windfall.com
%
% Created:      15 February 2005
%
%-----------------------------------------------------------------------------

\nonstopmode
\documentclass[natbib,authoryear,fleqn]{sigplanconf}
% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% authoryear    To obtain author/year citation style instead of numeric.
\usepackage{amsmath}
\usepackage{latexsym}
\usepackage{fancyvrb}
\usepackage{mathpartir}

\usepackage{todonotes}
%%\newcommand{\mytodo}[2][]{}
\newcommand{\mytodo}[2][]{\todo[color=gray!20,size=\scriptsize,fancyline,#1]{#2}}
\newcommand{\redtodo}[2][]{\todo[color=red!20,size=\scriptsize,fancyline,#1]{#2}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2TeX setup

%include polycode.fmt

% Avoid excessive amounts of whitespace in inline code.
%subst inline x = "\mbox{\ensuremath{" x "}}"

% Constructors.

\newcommand{\constructor}[1]{\textsf{#1}}
%format λ   = "\lambda"
%format .   = "\!."
%format not = "\Varid{not}"
%format ==  = "{==}"
%%format <=  = "{<=}"
%%%format -> = "→"
%format →   = "\mathrel{→}"
%format sp  = "\mkern-2mu"
%format : = "\!\!:\!"
%format 0    = "0"
%format 1    = "1"
%format 2    = "2"
%format 3    = "3"
%format 4    = "4"
%format 5    = "5"
%format 6    = "6"
%format Set₁ = Set "_1"
%format ∈     = "\mathrel{∈}"
%format ·     = "\mathrel{·}"
%format _∈_·_ = "{" _ "\mkern-5mu" ∈ "\mkern-5mu" _ "\mkern-3.4mu" · "\mkern-5mu" _ "}"
%format true  = "\constructor{true}"
%format false = "\constructor{false}"
%format trib  = "\mathord{\trib}"
%format trib0  = "\mathord{\trib}_0"
%format tribk = "\mathord{\trib^\kappa}"
%format trit  = "\mathord{\trit}"
%format tritk = "\mathord{\trit^\kappa}"
%format uk = "\!^\kappa"
%format k = "\kappa"
%format k' = "\kappa^\prime"
%format fixb = fix "_\bot"
%format star = "\star"
%format stari = "\star_i"
%format stark = "\star_\kappa"
%format stardep = "\star^{\Pi}"
%format stardepk = stardep "_{\kappa}"
%format _star_ = _ "\!" star "\!" _
%format pack (x) (y) = x "," y
%format <*> = "\circledast"
%format <*>! = <*> "_i"
%format <*>> = <*> "^\Pi"
%format <*>>! = <*> "^\Pi_i"
%format uj = "^j"
%format ui = "^i"
%format guardb = guard "_\bot"
%format forceb = force "_\bot"
%format guardt = guard "_\top"
%format forcet = force "_\top"
%%format hk = "\!\![\kappa]"
%format hk = "\!"
%%format <= = "\le"
%format t_0 = t "_0"
%format t_1 = t "_1"
%format jlti = "j\!<\!i"
%format e0 = e "_0"
%format e1 = e "_1"
%format e2 = e "_2"
%format Fixb = Fix "_\bot"
%format Fixt = Fix "_\top"
%format wtribi = "\triangleright_\bot^i"
%format wtriti = "\triangleright_\top^i"
%format mutri = "\mu^\blacktriangleright"
%format mu = "\mu"
%format nutri = "\nu^\blacktriangleright"
%format nu = "\nu"
%format foldtri = fold "^\blacktriangleright"
%format ut = "\!^\blacktriangleright"
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Unicode setup

\usepackage[english]{babel}
\usepackage[mathletters]{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

\DeclareUnicodeCharacter{"00B7}{\ensuremath{\cdot}}
\DeclareUnicodeCharacter{"2237}{\ensuremath{::}}
\DeclareUnicodeCharacter{"25C7}{\ensuremath{\Diamond}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\input{macros.tex}
\arraycolsep=1.4pt

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP '15}{September 1--3, 2015, Vancouver, British Columbia, Canada}
\copyrightyear{2015}
%% camera-ready data
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish,
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers,
                                  % short abstracts)

\titlebanner{banner above paper title}        % These are ignored unless
\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Total (Co)Programming with Guarded Recursion}
%%\subtitle{Subtitle Text, if any}

\authorinfo{Andrea Vezzosi}
           {Chalmers Univerisity of Technology}
           {vezzosi@@chalmers.se}
%% \authorinfo{Name2\and Name3}
%%            {Affiliation2/3}
%%            {Email2/3}

\maketitle

\begin{abstract}
In total functional (co)programming valid programs are guaranteed to
always produce (part of) their output in a finite number of steps.

Enforcing this property while not sacrificing expressivity has been
challenging. Traditionally systems like Agda and Coq have relied on a
syntactic restriction on (co)recursive calls, but this is inherently
anti-modular.
%% and sometimes leads to unexpected interactions with new
%% features.

Guarded recursion, first introduced by Nakano, has been recently
applied in the coprogramming case to ensure totality through typing
instead, by capturing through a new modality the relationship between
the consumption and the production of data.

In this paper we show how that approach can be extended to
additionally ensure termination of recursive programs, through the
introduction of a dual modality and the interaction between the
two. As in the coprogramming case, however, we need clock variables to
separate different flows of data. Existential quantification over
clocks then recovers inductive types from guarded ones, dually to how
universal quantification recovers coinductive types.

%% - guarded recursion
%% - new modality
%% - existential

\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
term1, term2

\keywords
keyword1, keyword2

\section{Introduction}

The standard termination checkers of systems like Coq or Agda rely on
syntactic checks, and while they employ additional heuristics, they mainly ensure that the recursive calls have
structurally smaller arguments.
%% To get a recursive program to pass the standard termination checkers
%% of systems like Coq or Agda, the recursive calls must have
%% structurally smaller arguments.
This is the case for the |map| function on lists:
\begin{code}
map : (A → B) → List A → List B
map f []        = []
map f (x ∷ xs)  = f x ∷ map f xs
\end{code}
Here the argument |xs| of |map f xs| is manifestly smaller than the original |(x ∷ xs)| because
it is a direct ``subtree'', so the definition is accepted.

However, such a syntactic check gets in the way of code reuse and
compositionality. This is especially the case when using
higher-order combinators, because they can appear between a recursive
call and the actual data it will process. The following definition of
a mapping function for rose trees is an example of this.

\begin{code}
data RoseTree A = Node A (List (RoseTree A))

mapRT : (A → B) → RoseTree A → RoseTree B
mapRT f (Node a ts) = Node (f a) (map (\ t -> mapRT f t) ts)
\end{code}
The definition of mapRT is not accepted because syntactically |t| has
no relation to |Node a ts|, we need to pay attention to the semantics of
|map| to accept this definition as terminating, in fact a common
workaround is to essentially inline the code for |map|\footnote{If the definition of |map| is available, Coq will attempt this automatically}.
\begin{code}
mapRT : (A → B) → RoseTree A → RoseTree B
mapRT f (Node a ts) = Node (f a) (mapmapRT f ts)
  where
    mapmapRT f []        = []
    mapmapRT f (t ∷ ts)  = mapRT f t ∷ mapmapRT f ts
\end{code}
Here we have spelled out the nested recursion as a function
|mapmapRT|, and the checker can figure out that |mapRT| is only going
from the call |mapRT f (Node a (t ∷ ts))| to |mapRT f t|, so it is accepted.

Such a system then actively fights abstraction, and offers few recourses
other than sticking to some specific ``design patterns'' for
(co)recursive definitions.
\mytodo{say something about increasingly complex heuristics?}
%%From that comes the temptation to put more
%%sophisticated heuristics into the checker, which from time to time
%%need to be retracted.\mytodo{expand on prolem with univalence? at least add citations}

Recently there has been a fair amount of research into moving the information about how functions consume and produce
data to the type level, so that totality checking can be more modular
\cite{BobConor}, \cite{Rasmus}, \cite{Andreas}. In particular the previous work on Guarded Recursion (\cite{BobConor},
\cite{Rasmus}) has handled the case of ensuring totality for
corecursion, i.e. manipulating infinite data. The issue
of ensuring totality in a modular way for recursion, over well-founded data, was however
left open. We address that problem by presenting a calculus that supports both corecursion
and recursion with a single guarded fixed point combinator.
\mytodo{say something about modalities/quantifiers?}


%%This paper extends to the case of recursion
%%the previous work on Guarded Recursion \cite{BobConor} \cite{Rasmus},
%%which was focused on corecursion and where inductive types were only
%%given their primitive recursor, by presenting a more relaxed model where
%%the connectives for guarded recursion can coexist with their duals.

We make the following contributions:
\begin{itemize}
\item We define a core type system which supports total programming by
  combining guarded recursion, existential and universal clock
  quantification and a new delay modality. From these primitives we
  can derive both (finitely branching) initial algebras and final
  coalgebras, i.e. inductive and coinductive datatypes. The type
  system is an extension of Martin L\"{o}f Type Theory.
\item We give an interpretation of the system into a relationally
  parametric model of dependent type theory \cite{atkey:param-model},
  drawing a parallel between clock quantification and parametric
  polymorphism.
\item In particular we show how existential types which support
  representation independence can be defined in a predicative system
  by truncating $\Sigma-$types to the universe of discrete reflexive
  graphs.
\end{itemize}

\subsection{Guarded Recursion}

The basic principle of Guarded Recusion is to keep track of the
guardedness information in the types. Going back to the rose tree
example we can give the data constructor |Node| a more precise type.
\begin{code}
Node : A -> (List (trib RoseTree A)) → RoseTree A
\end{code}
The type constructor |trib| makes explicit that the subtrees are
built, and can be consumed, in fewer time/steps than the resulting
tree. \mytodo{is time still a good metaphor? In the end this is all
  about well-founded induction, maybe I should be upfront about that
  from the start. !Time as a countdown! }

Once we've done that we can write |mapRT| by reusing |map|.
\begin{code}
mapRT : (A → B) → RoseTree A → RoseTree B
mapRT f (Node a ts) = Node a (map (\ t -> mapRT ut f t) ts)
\end{code}
Here the call |mapRT ut| stands for an implicit use of a guarded
fixpoint combinator we will introduce in Section \ref{fixb}, so it gets
type |(A -> B) -> trib RoseTree A → trib RoseTree B|, i.e. it can
only handle smaller trees but also produces smaller trees, so the
definition is well-typed. If we tried to write a circular definition like
\begin{code}
mapRT f ts = mapRT f ts
\end{code}
the types would not match because |ts| is of type |RoseTree A|
rather than |trib RoseTree A|.

In general we will have to deal with data of unrelated sizes, so
instead of |trib| we have a family of type constructors |tribk| indexed by clock
variables $\kappa$, which are introduced by the quantifiers |∀ k| and
|∃ k|.
Often we will leave the clocks implicit at the level of terms, however where appropriate we will use |λ| abstraction and application for |∀ k|, and the introduction |(pack)| and pattern matching for |∃ k|.
\begin{code}
(pack) : ∀ k . A hk -> ∃ k . A hk
\end{code}
The proper type of |Node| will then have a clock indexing the result
type |RoseTree uk|, which is the type of trees bounded in size by
the clock |k|.
\begin{code}
Node : ∀ k . A → List (tribk RoseTree uk A) → RoseTree uk A
\end{code}

As part of the interface of |tribk| we have the operation
\begin{code}
extract : ∀ k . tribk A -> A
\end{code}
which we overload for those |A| which mention |k| only in a strictly
positive position, in the model (Section \ref{sec:model}) it will correspond to monotonicity
with regard to time. Two particular cases are when |k| is not
free in |A| and when |A = tribk B| for any |B|.
\mytodo{only mention extract for k free in A, you never use anything else}
%% Another primitive operation is |guardb|.
%% \begin{code}
%% guardb : (∃ k . A) -> ∃ k . tribk A
%% \end{code}

%% Intuitively |guardb| tells us that we can always pick a clock that has
%% more time left than a given one, so that we can insert a |tribk| to
%% guard the value contained in the existential. It has an inverse that
%% we call |forceb|.

%% \begin{code}
%% forceb : (∃ k . tribk A) -> ∃ k . A
%% \end{code}


%% unfold example.
\mytodo{subsection?}

There are interesting uses of |tribk| even when not directly
associated with a datatype, an example of this is the |unfold|
function for |List|. We use |⊤| for the type with one element, and |+|
for the sum type with constructors |inl| and |inr|.
\begin{code}
unfold :  (∀ k . S hk -> ⊤ + (A × tribk S hk)) →
          ∀ k . S hk → List A
unfold f s = case f s of
               inl _          -> []
               inr (a , s')  -> a ∷ extract (unfold ut f s')
\end{code}
By restricting the type of the function |f| we are trying to unfold,
so that it always has to return a smaller next state |s'|, we can
guarantee termination. \mytodo{challenging for syntactic check because
s' not subterm of s} The use of |extract| is justified if we assume that |A| doesn't mention |k|.

Using |unfold| and a type of bounded natural numbers we can define the
function |downfrom|, which returns a list counting down to $1$.
\begin{code}
Zero  : ∀ k . Nat uk
Suc   : ∀ k . tribk Nat uk -> Nat uk

downfrom : ∀ k . Nat uk → List (∃ k . Nat uk)
downfrom =
  unfold   (λ k n ->   case n of
                                         Zero    -> Left _
                                         Suc n'  -> Right ((pack(k)(n)) , n'))
\end{code}
\mytodo{find other symbol for introduction of existentials}
The existential quantification allows us to forget the size
information of the naturals in the list, so that we do not have to keep
them synchronized with the clock |k| given to the function we unfold.


\subsection{Fixedpoint combinators}
\label{fixb}

So far we have seen directly recursive definitions, here we show the
fixed point combinator they are based on and how it is derived from
a more general one.

\begin{code}
fixb :  (∀ k . (tribk A hk -> tribk B hk) -> A hk -> B hk)
        -> ∀ k . A hk -> B hk
\end{code}

The combinator |fixb| is what we have implicitly used so far, and as
we have seen it is a good match for the definition of functions that
recurse on one of their arguments.

%% Idea: we have some finite time left, tribk guarantees you time, tritk makes you spend it.
%% tribk A ~ this A can be consumed in less time than you have left
%% tritk A ~ you need to spend some time to get at this A

More generally though we also want to support cases of productive
value recursion, like Haskell's |ones = 1 : ones|, as in the previous
works on guarded recursion. For this purpose we make use of the modality
|tritk|, the dual of |tribk|, to guard the recursion.

\begin{code}
fix :  (∀ k . tritk A hk -> A hk) -> ∀ k . A hk
\end{code}

Intuitively |tritk A hk| requires some time to be spent before the
data is accessible, as opposed to |tribk A hk| which instead
guarantees that enough time is available. It is then natural to
combine requirements and guarantees when they match, so we introduce
the combinator |star|, which can be used to define |fixb| in terms of
|fix|.

\begin{code}
_star_ : ∀ k . tritk (A hk -> B hk) -> tribk A hk -> tribk B hk

fixb f = fix (λ k r . f k (λ x . r stark x))
\end{code}
With a suitable type |Stream uk| we can then define |ones|.

\begin{code}
cons : ∀ k . tritk Stream uk A  -> Stream uk A

ones : ∀ k . Stream uk Nat
ones = fix (λ k xs . cons 1 xs)
\end{code}

Other examples involving |tritk| can be found in previous work that
focuses on coinduction \cite{BobConor} \cite{Rasmus}. An important
difference is that in the present work |tritk| is no longer an
applicative functor since |pure : ∀ k . A hk -> tritk A hk| is not
supported in general, e.g. not for |A = tribk B|, however we do still
support |<*>|.

\begin{code}
<*> :  ∀ k . tritk (A hk -> B hk) -> tritk A hk -> tritk B hk
\end{code}

\subsection{Inductive types}

In previous work on guarded recursion, coinductive types were obtained
by universal clock quantification over their guarded variant, e.g. |∀
k . Stream Nat uk| would be the type of coinductive streams. In the
present work we are able to dualize that result and obtain inductive types by
existential quantification of the guarded variant, e.g. |∃ k . Nat
uk|.

For now we will assume type-level recursion, in Section
\ref{sec:induction} we will reduce it to uses of |fix| on a universe of
types and construct initial algebras for suitable functors.

Here we show the natural numbers as the simplest example. The guarded
version |Nat uk| is defined using a sum type, to encode the two
constructors, and inserting |tribk| in front of the recursive
occurrence of |Nat uk|.

\begin{code}
Nat uk   = ⊤ + tribk Nat uk
Zero uk : Nat uk
Zero uk  = inl tt
Suc uk : Nat uk -> Nat uk
Suc uk   = λ n . inr n
\end{code}

Now we can bind the clock variable with an existential |Nat = ∃ k
. Nat uk| and show that |Nat| supports the expected iterator.

\begin{code}
fold : A -> (A -> A) -> Nat -> A
fold z f (pack (k) (n)) = fixb (\ k r n ->
  case n of
    inl _  -> z
    inr n  -> f (extract (r n)))
  k n
\end{code}

However it is not enough to package the clock to get the right type,
for example we risk having too many |Zero|s if we can tell the
difference between |(pack k (inl tt))| and |(pack k' (inl tt))| for two
different clocks |k| and |k'|.

The key idea is that values of type |∃ k . A| must keep abstract the
specific clock they were built with, exactly like weak sums in System
F. Intuitively Nat will not be the initial algebra of |(⊤ +)| unless |Nat ≅
T + Nat| holds, so we must be able to support both an interface and an
equational theory where clocks play no role.

In the calculus we will internalize this invariance over the packaged
clock as type isomorphisms that we will justify with a parametric
model (Section \ref{sec:model}). In the specific case of |Nat|, both |(pack k (inl tt))| and
|(pack k' (inl tt))| get sent to |inl tt| by the isomorphism, so we can
conclude they are equal.

%% In other models of guarded recursion, |∀ k| or analogous modalities
%% are modeled by categorical limits, so it wasn't a stretch to imagine
%% |∃ k| as a colimit, however the trick for them to meaningfully coexist
%% is to be parametric limits and colimits, as in \cite{parametric-limit}.

Once we scale up to a dependently typed language we will also be able
to implement an induction principle in terms of |fix| in Section
\ref{sec:induction}. However before that we will describe our
calculus, where we directly manipulate time values instead of clocks
to gain expressivity.

\mytodo{Maybe have an introduction subsection about the model too?}
\section{From Clocks to Time}
\label{sec:lang}
The notation we have used in the examples so far is closely modeled on
the one used in \cite{BobConor} and \cite{Rasmus}. In particular
clocks are a convenient abstraction over explicitly handling time values,
since we can use the same clock to refer to different amounts of type
depending on the context.

We can think of clock variables as indexes into an environment of
values of type |Time|. This environment however is not passed untouched to every
sub-expression, or simply added to by binders, it also gets updated at the index |k| by
the modalities |tritk| and |tribk| for the scope of their
arguments \mytodo{does this correspond to dynamic scope?}.
So the same clock variable represents different time values in different parts of a type expression.

%%A good
%%analogy is Haskell's |Reader| monad: a clock variable looks up the current value in the
%%environment, while |tritk| and |tribk| locally override it with a smaller one.

To clarify the flow of |Time| we adopt a syntax inspired by Sized
Types \cite{Andreas} instead. It will also offer more flexibility in
the dependent case. In fact the first step is to add to the dependently
typed language of Figure \ref{fig:TT} a new type |Time|, together with inequality
|(i j : Time) ⊢ i ≤ j| and zero |0 : Time| and successor |↑ : Time -> Time|
(Figure \ref{fig:Time}).

Universal quantification over |Time| is simply done with a dependent
function type, and the |tritk| modality is a corresponding bounded
version. As a result the type |∀ k . tritk Nat uk| becomes |(i :
Time) -> (j : Time) -> ↑ j ≤ i -> Nat uj|, where the smaller time |j|
is explicitly mentioned and passed as the time parameter of the
guarded natural numbers type.

In the following we use the shorthand |∀ i . A| in place of |(i :
Time) -> A| and |∀ j < i . A| in place of |(j : Time) -> ↑ j ≤ i ->
A|, and so we also omit the inequality proof in abstractions and
applications, writing |λ j| in place of |λ j (p : ↑ j ≤ i)| and |f j|
in place of |f j p|.

\mytodo{is there a more standard notation for $\Pi$? should I just
explain Agda's one?}

As an example the operator |<*>| can be given the following type,
which also makes the implementation something like the |S| combinator.
Given a smaller time |j| we get the values of |f| and |x| at that time
and apply one to the other.
\begin{code}
(<*>) :  ∀ i . (∀ j < i . A -> B)
         ->    (∀ j < i . A) -> (∀ j < i . B)
f <*>! x = λ j -> f j (x j)
\end{code}

With this formulation it is also easy to see how to generalize |<*>|
to the dependent case since we can get hold of |j| and pass that to
|x| to obtain a valid argument for the dependent type |B|:
\mytodo{maybe i don't need to give it a different name since it is strictly more general?}
\begin{code}
(<*>>) :  ∀ i . (∀ j < i . (x : A) -> B x)
          ->    (x : ∀ j < i . A) -> (∀ j < i . B (x j))
f <*>>! x = λ j -> f j (x j)
\end{code}

However the existential quantification |∃ i. A| for |Time|, shown in Figure \ref{fig:exists},
has to be distinct from a plain |Σ| type because allowing an
unrestricted first projection would let us observe the specific |Time|
contained. The difference between |∃ i . A| and |Σ (i : Time). A| is
that the former can only be eliminated into the universe |U|
which conspicuosly lacks a code for |Time| itself (Figure \ref{fig:codes}).
In the model we will see that |∃| is exactly a
"truncation" of the corresponding |Σ| to the universe |U|
\ref{sec:model}.
\mytodo{give some intuition for the Universe as the one of "discrete" types, as opposed to Time and U itself having higher structure?}
We also add a form of $\eta$ expansion for |∃ i|, which will be
necessary to ensure the proper computational behaviour for induction.

Dually to |tritk| we have that |tribk| corresponds to a bounded |∃|
and we allow similar shorthands |∃ (j < i). A| for |∃ j . ↑ j ≤ i ×
A| and |(pack j a)| for |(pack j (p , a))|.

As an example we show the implementation of |star|, where we can pattern match on |(pack j
x)| because the return type belongs to the universe |U|:
%%As an example we show the implementation of |star|, where the presence
%%of |El| on the return type ensures that we can the pattern match on |(pack j
%%x)|:
\begin{code}
(star) :  ∀ i . (∀ j < i . A -> El B)
          ->    (∃ j < i . A) -> El (∃ j < i . B)
f stari (pack j x) = (pack j (f j x))
\end{code}

The |fix| combinator is taken as a primitive (Figure \ref{fig:fix}) with an
associated equality describing how it unfolds. Such an equality is
justified by the model but would lead to loss of strong normalization
if used unrestricted as a computation rule. We discuss possible
solutions in Section \ref{sec:SN}.

We can also implement |extract| for |A : U|:
\begin{code}
extract : (A : U) -> ∀ i . (∃ j < i . El A) → El A
extract A i (pack j a) = a
\end{code}

\mytodo{guardb and forceb never used, rework this section not to mention?}
And implement a pair of basic conversion functions |guardb| and |forceb|:
\begin{code}
guardb : (∃ i . A(i)) -> ∃ i . ∃ (j < i). A(j)
guardb (pack i a) = (pack (↑ i) (pack i a))

forceb : (∃ i . ∃ (j < i). A(j)) → ∃ i . A(i)
forceb (pack i (pack j a)) = (pack j a)
\end{code}

The model justifies blessing |forceb| and |guardb| with the status of
isomorphism, together with the other canonical functions that witness
the isomorphisms of Figure \ref{fig:isos}.
In the case of |∀ i| we additionally have the usual isomorphisms that
can be implemented for dependent functions:

\begin{align*}
|∀ i. A × B |\, &|≅|\, |∀ i. A × ∀ i. B| \\
|∀ i. (x : A) → B|\, &|≅|\, |(x : A) → ∀ i . B| & |i ∉ fv(A)|\\
|∀ i. ∀ j. A|\, &|≅|\, |∀ j. ∀ i. A|\\
\end{align*}

%include rules.lagda

%% -

\section{Inductive Types}
\label{sec:induction}

In this section we will show how to implement the recursive type
equations we have used in terms of fixed points on the universe, then
the induction principle for |Nat|, and lastly we construct initial
algebras for any functor that properly commutes with |∃ i|.

\subsection{Recursive Type Equations}

For any function |F : U -> U| we can build |Fixb F : Time -> U| such
that |Fixb F i = F (∃ (j < i). Fixb F j)|.

The first step is to recognize that |∃ (j < i).| can take an element
of |∀ (j < i). U| as input rather than |U| or |Time -> U|, defining
the combinator |wtribi|.

\begin{code}
wtribi : (∀ (j < i). U) -> U
wtribi X = ∃ (j < i). X j
\end{code}

Using the time analogy for intuition, in a case where we have no time
left, so there's no |j < i|, we already know that |∃ (j < i). A|
is equivalent to |⊥| without having to know what |A| is, only if we
actually have time to spare we will look into it.

Given |wtribi| we can turn |F : U -> U| into |∀ i . (∀ (j < i). U) -> U| by
precomposition and define |Fixb| through |fix|, giving us the desired
property.

\begin{code}
Fixb = fix (λ i X . F (wtribi X))
\end{code}

In the same way we define |Fixt| by |wtriti|:
\begin{code}
wtriti : (∀ (j < i). U) -> U
wtriti X = ∃ (j < i). X j
\end{code}

\subsection{Induction on Nat}
To get a concrete feel for how we can reduce induction to |fix| we
show induction for the natural numbers.

First we redefine |Nat|, and show the definition of its constructors |Zero| and |Suc|:
\begin{code}
Nat = El (∃ i. Fixb (\ X . ⊤ + X))

Zero : Nat
Zero = (pack 0 (inl tt))

Suc : Nat -> Nat
Suc (pack i n) = (pack (↑ i) (inr (pack i n)))
\end{code}

Then we can define an induction principle for the type families |P :
Nat -> U| which live in the universe |U|, since we are restricted by
the elimination rule of |∃ i|.

\begin{code}
indNat :  (P : Nat -> U)
          -> P Zero -> (∀ n -> El (P n) -> El (P (Suc n)))
          -> (n : Nat) -> El (P n)
indNat P z s (pack i n) =
  fix (\ i rec n ->  case n of
                       inl tt          -> z
                       inr (pack j n)  -> s (pack j n) (rec j n)
       )
      i n
\end{code}

Reading carefully we see that |s (pack j n) (rec j n)| has type |El (P
(Suc (pack j n)))| which we can reduce to |El (P (pack (↑ j) (inr
(pack j n))))| while the expected type is |El (P (pack i (inr (pack j
n))))|.  We can however conclude that |(pack (↑ j) (inr (pack j n)))|
and |(pack i (inr (pack j n)))| are equal since they both get sent to
|(pack j n)| by the |∃ i . ⊤ + (∃ (j < i) . A) ≅ ⊤ + ∃ i. A|
isomorphism.

For an induction principle we also want the right computational
behaviour when applied to the constructors for the datatype. We have
that |indNat P z s Zero = z| simply by unfolding |fix| and reducing
the case distinction. However for
\begin{code}indNat P z s (Suc n) = s n (indNat P z s n)\end{code}
we also need to apply the $\eta$ rule for |∃|.
\begin{code}
indNat P z s (Suc n)
= indNat P z s (case n of (pack i n') -> (pack (↑ i) (inr (i , n'))))
= case n of (pack i n') -> indNat P z s (pack (↑ i) (inr (i , n')))
= case n of (pack i n') -> s (pack i n') (indNat P z s (pack i n'))
= s n (case n of (pack i n') -> (indNat P z s (pack i n')))
= s n (indNat P z s n)
\end{code}
\subsection{Internal Indexed Functors}

In order to prove the existence of initial algebras we define the
category of indexed types, in the universe |U|, with respect to some
context |Γ|.  For each |Γ ⊢ X : Type| we define the category of
|X|-indexed types with terms |Γ ⊢ A : X -> U| as objects and |Γ ⊢ f :
(x : X) -> El (A x) -> El (B x)| as morphisms, identities and
composition are defined as expected.
We also write |A ⇒ B| for |(x : X) -> El (A x) -> El (B x)| and leave
the index |x| implicit when only lifted pointwise.

An |X|-indexed functor |F| is then a pair of terms
\begin{code}
Γ ⊢ F₀ : (X -> U) -> (X -> U)
Γ ⊢ F₁ :  (A B : X -> U) ->
          (A ⇒ B) -> (F A ⇒ F B)
\end{code}
such that |F₁| preserves identities and composition.

As an example we can make |∃ (j < i).| into a |(Time × X)|-indexed
functor by defining |trib| like so:
\begin{code}
(trib)₀ : (Time × X → U) → (Time × X → U)
(trib)₀ A (i , x) = ∃ (j < i) . A (j , x)
\end{code}
the action on morphisms is also pointwise and the $\eta$ rule for |∃|
and |×| are enough to preserve identities and composition.
For any |X|-indexed functor |F| we define the |Time × X|-indexed
functor |F[trib -]| that threads the |Time| component to |trib|.
\begin{code}
F[trib A ]₀ (i , x) = F₀ (λ y. ∃ j < i. A y) x
\end{code}

\subsection{Guarded Initial Algebras}
For each |X|-indexed functor |F| we obtain the initial algebra of
|F[trib -]| by
\begin{code}
mutri F (i , x) = fix (\ i A x → F (\ y → ∃ (j < i) . A (j , x)) i x
\end{code}
so that |mutri F = F[trib mutri F]|.

The algebra |F[trib mutri F] ⇒ mutri F| is then simply the identity
and the morphism from any other algebra |f : F[trib A] ⇒ A| is also definable through
|fix|, which also ensures its uniqueness.
\begin{code}
foldtri :  (A : Time × X → U) ->
           (F[trib A] ⇒ A) → mutri F ⇒ A
foldtri A f (i , x) = fix (\ i foldtri m → f (F (foldtri star) m)) i x
\end{code}

\subsection{Initial Algebras}

Initial algebras can then be obtained by |\ x → ∃ i. mutri F (i , x)|
for those |X|-indexed functors |F| which weakly commute with |∃ i| in the following sense.

Definition 1. Let |F| be an |X|-indexed functor, we say that |F|
weakly commutes with |∃ i| if the canonical map
\begin{code}
(x : X)  → (∃ i . F [trib A] (i , x))
         → F (\ x' → ∃ i. A (i , x')) x
\end{code}
is an isomomorphism for every |A|.

Theorem 1. Let |F| be an |X|-indexed functor that weakly commutes with |∃
i|, then |mu F x = ∃ i. mutri F (i , x)| is the initial algebra of
|F|.

Proof (Sketch). From |F| weakly commuting with |∃ i| at type |mutri F| we
obtain an indexed isomorphism |F (mu F) ≅ mu F| and so in particular
an algebra |F (mu F) ⇒ F|, the morphism from any other algebra is
obtained from the one for |mutri| and inherits his uniqueness since
there's a bijection between algebra morphisms like in \cite{Rasmus}.
\begin{code}
fold : (A : I → U) -> (F A ⇒ A) → (mu F ⇒ A)
fold A f x (pack i m) = foldtri (\ (i , x) → A x)
                                (λ i₁ m → f (F extract m)) i x m
\end{code}

As a corollary we obtain initial algebras for all finitely-branching polynomial functors.
\mytodo{flesh out a bit}

\subsection{(Guarded) Final Coalgebras}
The above result can be dualized to obtain final coalgebras of
|X|-indexed functors |F| that commute with |∀ i|.

For each |X|-indexed functor |F| we obtain the final coalgebra of
|F[trit -]| by
\begin{code}
nutri F (i , x) = fix (\ i A x → F (\ y → ∀ (j < i) . A (j , x)) i x
\end{code}
so that |nutri F = F[trit nutri F]|.

Definition 2. Let |F| be an |X|-indexed functor, we say that |F|
weakly commutes with |∀ i| if the canonical map
\begin{code}
(x : X)  → F (\ x' → ∀ i. A (i , x')) x
         → (∀ i . F [trit A] (i , x))
\end{code}
is an isomomorphism for every |A|.

Theorem 2. Let |F| be an |X|-indexed functor that weakly commutes with |∀
i|, then |nu F x = ∃ i. nutri F (i , x)| is the final coalgebra of
|F|.

\mytodo{dependent elimination for |nu F| ?}
\subsection{Mixed Recursion-Corecursion}
\mytodo{catalan numbers example?}

\mytodo{when comparing with guarded recursive types, say that to
internalize the functoriality "sized types" style you'd need directed
type theory, which is a good technical reason to use clocks instead}

%% intro forms, suc : ∃ k. Nat^k -> ∃ k. Nat^k, elimination existential
%% - mixed recursion
%% - initial algebras /


%% gcd example? https://github.com/pigworker/MGS14/blob/master/Lec4Crib.agda


\section{Disclaimer}

The equational theory described in Section \ref{sec:lang} is quite
strong, making fixed points obtained by |fix| judgementally unique and
the type isomorphisms holding strictly. These equations are indeed
justified strictly by the model, however when fitting this into an
intensional type theory where equality is checked by normalization
some thought will be required.


\section{A Parametric Model}
\label{sec:model}

The type isomorphisms involving |∀ i| of Figure \ref{fig:isos}
express the intuition that values are constructed in a |Time|
invariant way, dually the ones involving |∃ i| on the intuition that
the only elimination principle for it is |Time| invariant.

Since Reynolds \cite{Reynolds}, Relational Parametricity
\mytodo{caps?} has been shown to be a good tool to capture invariance
properties of programs, initially applied to invariance of polymorphic
types under change of data representation, but also invariance under
change of units of measure \cite{Kennedy} or manipulations of vectors
under translations \cite{atkey:algebraic-indexed}.

The basic principle is that types get modeled as a pair of a set of
values and a relation over that set. The relation describes a property
that should be preserved when manipulating such values.

To model our language we then use the relationally parametric model of
dependent type theory from \cite{atkey:param}, defining |Time| as the
type of natural numbers related by |<=| and the universe |U| as
essentially small sets related by proof-irrelevant relations (their
"Small, Discrete, Proof Irrelevant Universe").

\subsection{Reflexive Graphs as a Category with Families}
Here we recap the basic structure of the model, which is formulated as
a Category with Families \cite{cwf}, and so defines a category \CxtF of
contexts, for each $\Gamma \in Obj(\CxtF)$ a collection $\TyF \Gamma$ of
semantic types, and for each $A \in \TyF \Gamma$ a collection $\TmF
\Gamma A$ of semantic terms.

The category $\CxtF$ in our case is the functor category $\CSet^\RG$,
where $\RG$ is the small category of Figure \ref{fig:RG}.  An object
$\Gamma$ of \CxtF is best thought of as a triple $(\Gamma_O, \Gamma_R,
\Gamma_{refl})$ where $\Gamma_O$ is a set of objects, $\Gamma_R$ is a binary
relation over $\Gamma_O$ and $\Gamma_{refl}$ is a function witnessing the
reflexivity of $\Gamma_R$.
\[
\begin{array}{l l}
\Gamma_O & : Set \\
\Gamma_R & : \Gamma_O × \Gamma_O \to Set \\
\Gamma_{refl} & : \forall \gamma \in \Gamma_O.\; \Gamma_R(\gamma,\gamma)\\
\end{array}
\]
Morphisms $f : \Gamma \to \Delta$ are then a pair of functions $f_o$
and $f_r$ which commute with reflexivity:
\begin{gather*}
f_o : \Gamma_O \to \Delta_O \\
f_r : \forall \gamma_0, \gamma_1 \in \Gamma.\; \Gamma_R(\gamma_0,\gamma_1) \to \Delta_R(f_o(\gamma_0), f_o(\gamma_1)) \\
\mbox{such that}\\
\forall \gamma \in \Gamma_O.\; f_r (\Gamma_{refl}(\gamma)) = \Delta_{refl} (f_o(\gamma))
\end{gather*}
These morphisms assume the role of substitutions, mapping environments
of the context $\Gamma$ into environments of $\Delta$. We use the
notations $A\{f\}$ and $M\{f\}$ to apply the substitution $f$ to the type
$A$ and term $M$.


Since $\CxtF$ is a functor category into $\CSet$ it inherits a standard
Category with Families structure(\cite{Hoffman}) including definitions
for the standard connectives, most of them lifted pointwise from
\CSet, here we will mention only enough to explain our connectives.

The collection $\TyF \Gamma$ of types then consists of families of reflexive
graphs, so $A \in \TyF \Gamma$ is again a triple $(A_O,A_R,A_{refl})$
but each component is indexed by the corresponding one from $\Gamma$ to allow types to depend on values from the environment.
\begin{gather*}
A_O : \Gamma_O \to Set \\
A_R : \forall \gamma_0 , \gamma_1 \in \Gamma,\; \Gamma_R(\gamma_0,\gamma_1) \to A_O(\gamma_0) × A_O(\gamma_1) \to Set \\
A_{refl} : \forall \gamma \in \Gamma,\; \forall a \in A_O(\gamma).\; A_R(\Gamma_{refl}(\gamma),a,a)
\end{gather*}

The empty context $\epsilon \in Obj(\CxtF)$ is defined as the
singleton reflexive graph $\epsilon = (\{*\},(λ \, \_ \, \_ \, . \, \{*\}),(λ \, \_ \, \_ \, . \, *))$
so an element of $Ty(\epsilon)$ corresponds to an object of \CxtF.

We can also extend a context $\Gamma$ by a type $A \in \TyF \Gamma$ to
obtain another context $\Gamma.A$ by pairing up each component, so
that we have a map $\tfst : \Gamma.A \to \Gamma$ which projects out the
first component and functions as a weakening substitution.

Finally an element $M$ of $\TmF \Gamma A$ correponds to a map $\Gamma \to \Gamma.A$ such that $\tfst \circ M = id_\Gamma$:
\begin{gather*}
M_o : \forall \gamma \in \Gamma_O, \; A_O(\gamma)\\
M_r : \forall \gamma_0, \gamma_1 \in \Gamma_O, \; \forall \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), \; A_R(\gamma_r,M_o(\gamma_0),M_o(\gamma_1)) \\
\mbox{such that}\\
\forall \gamma \in \Gamma_O, \; M_r (\Gamma_{refl}(\gamma)) = A_{refl}(\Gamma_{refl}(\gamma),M_o (\gamma))\\
\end{gather*}

\subsubsection{A Small, Discrete, Proof Irrelevant Universe}

In order to recover standard parametricity results like the free
theorems from Wadler \cite{Wadler}, Atkey et. al define a universe $U
\in \TyF \Gamma$ to connect the relations of the reflexive graphs to
the equality of their set of objects.

In particular for each $A \in \TmF \Gamma U$ we get a type $\El A \in
\TyF \Gamma$ such that for all we have that $(\El A)_O$ is a family of
small sets, $(\El A)_R$ is a family of proof irrelevant relations, and
for all $\gamma \in \Gamma_O$ we have that $(\El A)_R(\Gamma_{refl}(\gamma))$
is the equality relation of $(\El A)_O(\gamma)$.
Where the latter two requirements are to be considered up to isomorphism.

One main feature of $U$ is exemplified by considering a term $M \in
\TmF{\Gamma.A}{(\El B)\{\tfst\}}$ where $A \in \TyF \Gamma$ and $B \in
\TmF \Gamma U$, i.e. where the type of the result is in the universe
and doesn't depend on $A$.
Unfolding the application of $\tfst$ and unpacking the environment for $\Gamma.A$ we get the following for the components $M$,
where the condition of commuting with reflexivity is between two elements of
a proof-irrelevant relation, so can be omitted.
\[
\begin{array}{l c l}
M_o &:& \forall \gamma \in \Gamma_O, \; \forall a \in A_O(\gamma), \; (\El B)_O(\gamma) \\
M_r &:& \forall \gamma_0, \gamma_1 \in \Gamma_O, \;
      \forall \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), \; \\
      & &\forall a_0 \in A_O(\gamma_0), a_1 \in A_O(\gamma_1), \;
      \forall a_r \in \A_R(\gamma_r,a_0,a_1), \; \\
       & &(\El B)_R(\gamma_r, M_o(\gamma_0,a_0), M_o(\gamma_1,a_1))\\
\end{array}
\]
We see that the result of $M_r$ doesn't mention $a_r$ because $\El B$ doesn't depend on $A$, moreover if
we specialize $\gamma_r$ to $\Gamma_{refl}(\gamma)$ we get $(\El
B)_R(\Gamma_{refl}(\gamma), M_o(\gamma,a_0), M_o(\gamma,a_1))$, which we
know to be isomorphic to $M_o(\gamma,a_0) = M_o(\gamma,a_1)$ so we can conclude
the following:
\begin{gather*}
\forall \gamma \in \Gamma_O, \;
      \forall a_0, a_1 \in \Gamma_O, \;
      \forall a_r \in \A_R(\Gamma_{refl}(\gamma),a_0,a_1), \; \\
        M_o(\gamma,a_0) = M_o(\gamma,a_1)
\end{gather*}
In other words, for a fixed $\gamma$, we have that $M_o$ considers any
two related $a_i$ as being equal, since it returns the same result.

The universe $U$ is shown to contain product and sum types, natural
numbers, to be closed under $\Sigma$ types and to contain $\Pi (x :
A). \El (B x)$ for any small type $A$.
\mytodo{too imprecise? also assuming small sets are closed over similar stuff}

%% Another important feature of $U$ corresponds to Reynolds' identity
%% extension lemma. In fact a map like $T : U \to U$, which could
%% e.g. be a type constructor like |List|, has a relation component $T_r$
%% which is equality preserving, bla blah

\subsection{Interpretation of the Language}
We are left with having to interpret our own primitives.

\subsubsection{|Time|}

The type |Time| is intepreted as the reflexive graph of natural
numbers with $n \le m$ as the relation, each number represents how
many steps of computation we have left:
\begin{gather*}
\Time_O = ℕ\\
\Time_R(n,m) = \{ * \mid n \le m \}\\
\Time_{refl}(n) = *\\
\end{gather*}
The terms for |0| and |↑| are then implemented by $0$ and $+1$ on the underlying naturals.
\mytodo{max?}

The fixpoint operator |fix| and its uniqueness are then a simple matter of
well-founded induction on the natural numbers.

From the observation above about terms of a non dependent type we
already get that a term $M \in \TmF {\Gamma.\Time} {(\El B)\{\tfst\}}$ is
going to produce the same result no matter what natural number it gets
from the environment, since they are all related, which justifies the isomorphism $∀ i. \El
B ≅ \El B$ of our language.\mytodo{mention that Pi types are naturally isomorphic to open terms?}

The relation between times |i ≤ j| is then intepreted by $\Le : \TyF
(\Time.\Time\{\tfst\})$, which also fits in $U$ since it has no
interesting inhabitants.
\begin{gather*}
\Le_O(n , m) = \{ * \mid n \le m \} \\
\Le_R(\_,\_) = \{*\}\\
\Le_{refl}(\_) = *
\end{gather*}

\subsubsection{Representationally Independent Existential}

We will ultimately define the existential quantification over |Time|
in the same style as a parametric colimit in the sense of Reddy
\cite{parametric-limits}.

However we will show a connection with the standard $\Sigma$ type by
first defining a general operation to convert any small reflexive
graph into a discrete and proof-irrelevant one.

Given a small $A \in \TyF \Gamma$ we define $\Tr A \in \TmF \Gamma U$
which we call the discrete truncation of $A$.

We first give some preliminary definitions on reflexive graphs, and
then lift those to the case of families to define $\Tr$.
For a reflexive graph $A \in Obj(\CxtF)$ we define $A_O/A_R$ to be the
set obtained by quotienting $A_O$ with the symmetric transitive closure of $A_R$ which we denote $A_R^*$.
Moreover we define $\LiftF_{A,B}(R)$ to lift a relation $R : A_O \to
B_O \to Set$ to a relation $A_O/A_R \to B_O/B_R \to Set$, so that we have
a function $\liftF_R : \forall a, b. \, R(a,b) →
\LiftF_{(A,B)}(R)([a],[b])$.
\begin{gather*}
\begin{array}{l c l}
\LiftF &:& \forall A, B \in Obj(\CxtF), \forall (R : A_O \to B_O \to Set),\\
       & & A_O/A_R \to B_O/B_R \to Set \\
\end{array}\\
\LiftF_{(A,B)}(R : A_O \to B_O \to Set)([ a ],[ b ])\\
\begin{array}{l c l c l}
  &=& \{ (a',\tilde{a} ,b',\tilde{b},r) &\mid& a' \in A_O, \tilde{a} \in A_R^*(a,a'),\\
  & & & &b' \in B_O, \tilde{b} \in B_R^*(b,b'),\\
  & & & &r \in R(a',b') \}/\top\\
\end{array}
%% \LiftF_{(A,B)}(R : A_O \to B_O \to Set)(qa,qb) = \{ * \mid ∃ a. a \in [qa], ∃ b. b \in [qb], R(a,b) \} \\
%% \mbox{alternatively (by definition on the representatives)}\\
%% \LiftF_{(A,B)}(R : A_O \to B_O \to Set)([ a ],[ b ]) = \{ * \mid ∃ a'. A_R^*(a,a'), ∃ b'. B_R^*(b,b'), R(a',b') \} \\
\end{gather*}
Picking the representatives $a$ and $b$ is justified because we
produce loically equivalent relations for related elements.
We have that $\LiftF_{A,B}(R)$ is proof irrelevant by construction
since we define it as a quotient with the total relation which we name $\top$,
moreover $\LiftF_{(A,A)}(A_R)(q_0,q_1)$ is logically equivalent to $q_0
=_{A_O/A_R} q_1$.

\mytodo{prove? could be lifted from Uday Reddy}

Finally we use the definitions above to define $\Tr A$ for a given $A \in Ty(\Gamma)$:
\begin{gather*}
(\Tr A) : \TmF \Gamma U\\
(\Tr A)_o(\gamma) = (A_O(\gamma)/A_r(\Gamma_{refl}(\gamma)),  \LiftF(A_r(\Gamma_{refl}(\gamma)))) \\
(\Tr A)_r(\gamma_r) = \LiftF(A_r(\gamma_r))
\end{gather*}
we have to show that $(\Tr A)_o$ and $(\Tr A)_r$ commute with reflexivity,
\begin{gather*}
\forall \gamma, U_{refl}((\Tr A)_o(\gamma)) = (\Tr A)_r(\Gamma_{refl}(\gamma))
\end{gather*}
but $U_{refl}$ simply projects out the relation given as the second
component of the tuple, so both sides reduce to
$\LiftF(A_r(\Gamma_{refl}(\gamma)))$ and we are done.

Remark, for any $A \in \TmF \Gamma U$, the types $\El A$ and $\El (\Tr
A)$ are equivalent. In fact $A_r(\Gamma_{refl}(\gamma)$ is already
equivalent to equality for $A_O(\gamma)$ so the quotient
$A_O(\gamma)/A_r(\Gamma_{refl}(\gamma))$ is equivalent to
$A_O(\gamma)$, and for the same reason $\LiftF(A_r(\gamma_r))$ is
equivalent to $A_r(\gamma_r)$.

The next step is to define an introduction and an elimination for $\Tr
A$; the former sends an element of $A$ to its equivalence class:
\begin{gather*}
\tr : \TmF {A} {\El (\Tr A)}  \\
\tr_o(a) = [ a ]\\
\tr_r(a_r) = \liftF(a_r)
\end{gather*}
We then have dependent elimination of $\Tr A$ into other types $B \in
\TmF {\Gamma.\El (\Tr A)} {U}$ that live in the universe.
Given a $t \in \TmF {\Gamma.A} {\El B\{\tfst,\tr\}}$ we define $\elim$:
\begin{gather*}
\elim : \TmF {\Gamma.\El (\Tr A)} {\El B}\\
\elim_o(\gamma,[ a ]) = t_o(\gamma,a)\\
\elim_r(\gamma_r, [ (a',\tilde{a},b',\tilde{b},r) ]) = t_r(\gamma_r,r)
\end{gather*}
This definition begs the questions of why we are allowed to work with
the representatives of these quotients and why $t_r(\gamma_r,r)$ is
even a member of the expected relation, both of these problems are
solved by the discreteness of $B$.
First we unfold the type of $t_r$,
\[
\begin{array}{l c l}
t_r &:& \forall \gamma_0, \gamma_1 \in \Gamma_O, \; \gamma_r \in \Gamma_R(\gamma_1,\Gamma_2), \;\\
    & & \forall a_0 \in A_O(\gamma_0), a_1 \in A_O(\gamma_1), a_r \in A_R(\gamma_r,a_0,a_1),\; \\
    & & (\El B)_R((\gamma_r,\liftF(a_r)), t_o(\gamma_0,a0), t_o(\gamma_1,a_1))
\end{array}
\]
and note that in particular for any $\gamma \in \Gamma_O$ we can take
$\gamma_r = \Gamma_{refl}(\gamma)$ and obtain an equality
$t_o(\gamma,a0) = t_o(\gamma,a_1)$ for any two related $a_0, a_1 \in
A_R(\gamma)$. This follows from proof-irrelevance of $(\Tr A)_R$,
giving us $\liftF(a_r) = (\Tr A)_{refl}([a])$, and discreteness of
$(\El B)$.

To justify the definition of $\elim_o$ we have to show that for two
$a_0, a_1 \in A_O(\gamma)$ related by $a_r \in
A_R(\Gamma_{refl}(\gamma),a_0,a_1)$, we have $t_o(\gamma,a_0) =
t_o(\gamma,a_1)$; but this follows directly from the observation about $t_r$

In the case of $\elim_r$ we already know that we will produce the same
result for different representatives, because of proof-irrelevance,
but it is less obvious that it belongs in $(\El B)_R(\gamma_r,[
(a',\tilde{a},b',\tilde{b},r) ]), t_o(\gamma_0,a), t_o(\gamma_1,b))$. We know
that $t_r(\gamma_r,r) \in (\El B)_R(\gamma_r,\liftF(r)),
t_o(\gamma_0,a'), t_o(\gamma_1,b'))$, and from the observation about
$t_r$ we know that $t_o(\gamma_0,a) = t_o(\gamma_0,a')$ and
$t_o(\gamma_0,b) = t_o(\gamma_0,b')$, so also have $t_r(\gamma_r,r)
\in (\El B)_R(\gamma_r,\liftF(r)), t_o(\gamma_0,a), t_o(\gamma_1,b))$,
and since $\liftF(r) = [ (a',\tilde{a},b',\tilde{b},r) ]$ by proof-irrelevance,
we obtain the result we wanted.



To define the existential we can then simply truncate the
corresponding $\Sigma$ type,
\[ ∃ i . A = \Tr (\Sigma i : Time. A) \]
so that |(pack i a)| is interpreted as the introduction for $\Sigma$
followed by $\tr$, while the case expression is interpreted as $\elim$
combined with the projrections of $\Sigma$.

More generally we could consider $∃ (x : A) . B = \Tr (\Sigma x :
A. B)$. If both $A$ and $B$ belong in $U$ then $∃ (x : A) . B$ is
equivalent to $\Sigma (x : A) . B$, which reproduces the standard
result about recovering strong sums from weak ones by parametricity.



%% - Describe Problem
%%    - problem 1: replace syntactic checks
%%            - examples of anti-modularity?
%%               - rose tree
%%               - div for later
%%            - inconsistencies? with univalence i mean
%%            - too much stuff? Write it, can be moved.
%%    - problem 2: guarded recursion applied only to corecursion
%%       - coinductive types defined with guards and fixpoints but inductive types as primitive

%% - List the contributions
%%   - dualize! (find better name than codelay)
%%   - allows codelay and existential -- why no codelay and pure for delay?
%%   - extension on MLTT with delay and codelay mod, fixpoints on universes, quantifiers over clock variables.
%%   - denotational model based on logical relations/parametricity
%%   - existential quant. as representationally independent one via relational truncation
%%  \ref{termination-univ-Agda} \ref{termination-univ-Coq}

%% \Section{2}
%%   - guarded rose-tree example, don't show fix
%%   - how do you really write introductions for e.g. nil, or zero,  oh actually (A ~ ∃ k, A) when k free in A
%%   - dualize! but
%%   - why different kind of semantics? (i.e. no CPO), ``i don't like non-termination''
%%   - comparing
%%      - model makes us give up general pure : a -> delay a
%%      - example hard to do with sized types? mostly reasoning, or for coinduction something from the HOL paper
%%                                          also hard to ``forget'' sizes (find example?)
%%                                          - recognizers! Recognizers.agda
%%      - big difference with BobConorRasmus, arrow types are not kripke, cite neelk's frp lang?
%%   - formalized irrelevancy of accessibility proofs(?)
%%   - try to define a universe ala induction-recursion. ala guardedness-preserving, see release notes.
%%   - apparently we can do nested/mixed recursion, see CatSZ.agda

\mytodo{underline where the sized-types notation helps consistently}

\appendix
\section{Appendix Title}

This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\begin{thebibliography}{}
\softraggedright

\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
P. Q. Smith, and X. Y. Jones. ...reference text...

\end{thebibliography}


\end{document}

%                       Revision History
%                       -------- -------
%  Date         Person  Ver.    Change
%  ----         ------  ----    ------

%  2013.06.29   TU      0.1--4  comments on permission/copyright notices
