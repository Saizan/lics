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

%\nonstopmode
\documentclass[natbib,authoryear,fleqn,preprint]{sigplanconf}
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
\newcommand{\mytodo}[2][]{}
%%\newcommand{\mytodo}[2][]{\todo[color=gray!20,size=\scriptsize,fancyline,#1]{#2}}
%%\newcommand{\redtodo}[2][]{\todo[color=red!20,size=\scriptsize,fancyline,#1]{#2}}
\usepackage{hyperref}
% Note that the \doi command from the doi package doesn't enable the
% same kinds of line breaks as the command below. Note also that the
% sigplanconf package defines a \doi command; my redefinition should
% be placed after the use of \doi{...} above.
\renewcommand{\doi}[1]{doi:\href{http://dx.doi.org/#1}{%
\urlstyle{same}\nolinkurl{#1}}}
% Turn off hyperlink borders.
\hypersetup{pdfborder=0 0 0}
% The pdfborderstyle option can be used to override the pdfborder
% option, so let's set it explicitly.
\hypersetup{pdfborderstyle={}}


\usepackage{amsthm}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}{Proposition}[section]
\newtheorem{corollary}{Corollary}[theorem]
\newtheorem{lemma}[theorem]{Lemma}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]

\theoremstyle{remark}
\newtheorem*{remark}{Remark}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% lhs2TeX setup

%include polycode.fmt

% Avoid excessive amounts of whitespace in inline code.
%subst inline x = "\mbox{\ensuremath{" x "}}"

% Constructors.

\newcommand{\constructor}[1]{\textsf{#1}}
%format fixlt = "\tfix_\trit"
%format λ   = "\lambda"
%format .   = "\!."
%format not = "\Varid{not}"
%format ==  = "{==}"
%%format <=  = "{<=}"
%%%%format -> = "\to"
%format U = "\U{}"
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
%format fixb = "\tfix_\elater"
%format star = "\star"
%format stari = "\star_i"
%format starj = "\star_j"
%format stark = "\star_\kappa"
%format stardep = "\star^{\Pi}"
%format stardepk = stardep "_{\kappa}"
%format _star_ = _ "\!" star "\!" _
%format pack (x) (y) = x "," y
%format <*> = "\circledast"
%format ast = <*>
%format merge = "\oplus"
%format <*>! = <*> "_i"
%format <*>> = <*> "^\Pi"
%format <*>>! = <*> "^\Pi_i"
%format uj = "^j"
%format ui = "^i"
%format guardb = "\mathsf{guard}_\elater"
%format forceb = "\mathsf{force}_\elater"
%format guardt = "\mathsf{guard}_\flater"
%format forcet = "\mathsf{force}_\flater"
%format uncurry = "\mathsf{uncurry}"
%format case = "\mathsf{case}"
%format of = "\mathsf{of}"
%format El = "\El"
%format ∃ = "\mathsf{\exists}"
%%format hk = "\!\![\kappa]"
%format hk = "\!"
%%format <= = "\le"
%format t_0 = t "_0"
%format t_1 = t "_1"
%format jlti = "j\!<\!i"
%format e0 = e "_0"
%format e1 = e "_1"
%format e2 = e "_2"
%format Fixb = "\mathsf{Fix}_\elater"
%format Fixt = "\mathsf{Fix}_\flater"
%format indNat ="\mathsf{indNat}"
%format wtribi = "\elatercode^i"
%format wtriti = "\flatercode^i"
%format mutri = "\mu^\elater"
%format mu = "\mu"
%format nutri = "\nu^\flater"
%format nu = "\nu"
%format foldtri = fold "^\elater"
%format ut = "\!^\elater"
%format cat = "\mathsf{cat}"
%format cat' = "\mathsf{cat^\prime}"
%format catt = "\mathsf{cat}^\flater"
%format catb = "\mathsf{cat}^\elater"
%format Time = "\Time"
%format extract = "\mathsf{extract}"
%format Nat = "\mathsf{Nat}"
%format Zero = "\mathsf{Zero}"
%format Suc = "\mathsf{Suc}"
%format inl = "\mathsf{inl}"
%format inr = "\mathsf{inr}"
%format tt = "\mathsf{tt}"
%format fold = "\mathsf{fold}"
%format List = "\mathsf{List}"
%format downfrom = "\mathsf{downfrom}"
%format unfold = "\mathsf{unfold}"
%format RoseTree = "\mathsf{RoseTree}"
%format Node = "\mathsf{Node}"
%format mapRT = "\mathsf{mapRT}"
%format map = "\mathsf{map}"
%format mapmapRT = "\mathsf{mapmapRT}"
%format fix = "\mathsf{fix}"
%format Stream = "\mathsf{Stream}"
%format cons = "\mathsf{cons}"
%format ones = "\mathsf{ones}"
%format pure = "\mathsf{pure}"
%format knotinfvA = "\kappa \not\in \mathsf{fv}(A)"
%format ⊤ = "\top"
%format limit = "\mathsf{limit}"

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

%%\conferenceinfo{ICFP '15}{September 1--3, 2015, Vancouver, British Columbia, Canada}
%%\copyrightyear{2015}
%% camera-ready data
%%\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
%%\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish,
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers,
                                  % short abstracts)

%%\titlebanner{banner above paper title}        % These are ignored unless
%%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Total (Co)Programming with Guarded Recursion}
%%\subtitle{Subtitle Text, if any}
%%\authorinfo{}{}{}

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

Guarded recursion, first introduced by Nakano, has been recently
applied in the coprogramming case to ensure totality through typing
instead. The relationship between the consumption and the production
of data is captured by a delay modality, which allows to give a safe
type to a general fixpoint combinator.

Here we show how that approach can be extended to additionally ensure
termination of recursive programs, through the introduction of a dual
modality and the interaction between the two. We recast the fixpoint
combinator as well-founded induction with additional invariance
guarantees, which we justify through a parametric model.

We obtain a dependently typed calculus which modularly ensures
totality for both coinductive and (finitely branching) inductive
types.

\end{abstract}

%%\category{F.3.3}{Logics and Meanings of Programs}{Studies of Program Constructs}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%term1, term2

\keywords
Dependent Type Theory, Guarded Recursion, Induction, Coinduction, Type-based termination

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
mapRT f (Node a ts)
  = Node (f a) (map (\ t . mapRT f t) ts)
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
\cite{atkeyMcBride:icfp13,mogelberg:csllics14,abelPientka:icfp13}. In particular the previous work on Guarded Recursion \cite{atkeyMcBride:icfp13,
mogelberg:csllics14} has handled the case of ensuring totality for
corecursion, i.e. manipulating infinite data. The issue
of ensuring totality in a modular way for recursion, over well-founded data, was however
left open. We address that problem by presenting a calculus that supports both corecursion
and recursion with a single guarded fixed point combinator.
\mytodo{say something about modalities/quantifiers?}


%%This paper extends to the case of recursion
%%the previous work on Guarded Recursion \cite{atkeyMcBride:icfp13} \cite{mogelberg:csllics14},
%%which was focused on corecursion and where inductive types were only
%%given their primitive recursor, by presenting a more relaxed model where
%%the connectives for guarded recursion can coexist with their duals.

We make the following contributions:
\begin{itemize}
\item We define a core type system which supports total programming by
  combining guarded recursion, existential and universal \Time{}
  quantification and a new delay modality. From these primitives we
  can derive both (finitely branching) initial algebras and final
  coalgebras, i.e. inductive and coinductive datatypes. The type
  system is an extension of Martin-L\"{o}f Type Theory.
\item We give an interpretation of the system into a relationally
  parametric model of dependent type theory in reflexive graphs \cite{atkeyGhaniJohann:popl14},
  drawing a parallel between \Time{} quantification and parametric
  polymorphism.
\item In particular we show how existential \Time{} quantification supporting
  representation independence can be defined in a predicative system
  by truncating $\Sigma$ types to the universe of discrete reflexive
  graphs.
\end{itemize}

\subsection{Guarded Recursion}

The basic principle of Guarded Recursion is to keep track of the
termination information in the types. Going back to the rose tree
example we can give the data constructor |Node| a more precise type.
\begin{code}
Node : A -> (List (trib RoseTree A)) → RoseTree A
\end{code}
We use the modality |trib| to explicitly mark the recursive occurrence
of |RoseTree A|. Because of this the subtrees have a type that differs from the
root, and we will be able to keep track of which recursive calls are valid.

Once we've done that we can write |mapRT| by reusing |map|.
\begin{code}
mapRT : (A → B) → RoseTree A → RoseTree B
mapRT f (Node a ts) = Node a (map (\ t . mapRT ut f t) ts)
\end{code}
Here the call |mapRT ut| stands for an implicit use of a guarded
fixpoint combinator we will introduce in Section \ref{fixb}, so it gets
type |(A -> B) -> trib RoseTree A → trib RoseTree B|, i.e. it can
only handle smaller trees but also produces smaller trees, so the
definition is well-typed. If we tried to write a circular definition like
\begin{code}
mapRT f ts = mapRT ut f ts
\end{code}
the types would not match because |ts| is of type |RoseTree A|
rather than |trib RoseTree A|.

We can explain the meaning of |trib A| using a countdown metaphor: if
we consider that we have a finite amount of time |i| left to complete
our computation, a value of type |trib A| tells us that there is a
future time |j| at which we have a value of type |A|. So in
particular, even if we take |A| to be the unit type |⊤|, the type
|trib ⊤| is not necessarily inhabited, because we might have no time
left. Considering that our times are counting down to |0| we say that future
times are smaller.

In general we will have to deal with data on unrelated timelines, so
instead of |trib| we have a family of type constructors |tribk| indexed by clock
variables $\kappa$, which are introduced by the quantifiers |∀ k| and
|∃ k|.
Often we will leave the clocks implicit at the level of terms, however where appropriate we will use |λ| abstraction and application for |∀ k|, and the constructor |(pack)| and pattern matching for |∃ k|.
\begin{code}
(pack) : ∀ k . (A hk -> ∃ k . A hk)
\end{code}
The proper type of |Node| will then have a clock indexing the result
type, which becomes |RoseTree uk A| i.e. the type of trees bounded by
the clock |k|.
\begin{code}
Node : ∀ k . A → List (tribk RoseTree uk A) → RoseTree uk A
\end{code}

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
fix :  (∀ k . tritk A -> A) -> ∀ k . A
\end{code}
Using the time metaphor, a value of type |tritk A| gives us an |A| at every time in the future.

With a suitable type |Stream uk| we can then define |ones|.
\begin{code}
cons : ∀ k . A -> tritk Stream uk A  -> Stream uk A

ones : ∀ k . Stream uk Nat
ones = fix (λ k xs . cons 1 xs)
\end{code}

Other examples involving |tritk| can be found in previous work that
focuses on coinduction \cite{atkeyMcBride:icfp13} \cite{mogelberg:csllics14}. An important
difference is that in the present work |tritk| is no longer a full
applicative functor.
In fact while we do still support |<*>|,
\begin{code}
<*> :  ∀ k . tritk (A hk -> B hk) -> tritk A hk -> tritk B hk
\end{code}
we do not support |pure| in general, e.g. not at type |tribk A|,
but we do for those types that do not mention |k|:
\[
\begin{array}{l r}
|pure : ∀ k . A -> tritk A| & \quad\quad |knotinfvA|
\end{array}
\]
In the language of Section \ref{sec:lang} such an operation will be
implementable for a more general class of types, which will correspond
to those antitone with regard to time in the model of Section
\ref{sec:model}.

The interface of |tribk| is composed of two operations, |star| and |extract|.

If we have a function at any time in the future |tritk (A -> B)| and
an argument at some time in the future |tribk A|, we can apply one to the other with the combinator
|star|,
\begin{code}
star : ∀ k . tritk (A -> B) -> tribk A hk -> tribk B hk
\end{code}
which in particular can be used to define |fixb| in terms of
|fix|
\begin{code}
fixb f = fix (λ k r . f k (λ x . r stark x))
\end{code}

Lastly, as a dual of |pure|, we have |extract|,
\[
\begin{array}{l r}
\mathsf{extract} : \forall \kappa .~ \elater^\kappa A \to A & \quad\quad |knotinfvA|
\end{array}
\]
which allows to get values out of the |tribk| modality as long as their
type is independent of the clock |k|.

%% unfold example.
\subsection{Well-founded unfolding}

There are interesting uses of |tribk| even when not directly
associated with a datatype, an example of this is the |unfold|
function for |List|. We use |⊤| for the type with one element, and |+|
for the sum type with constructors |inl| and |inr|.
\begin{code}
unfold :  (∀ k . S hk -> ⊤ + (A × tribk S hk)) →
          ∀ k . S hk → List A
unfold f s = case f s of
               inl _         -> []
               inr (a , s')  -> a ∷ extract (unfold ut f s')
\end{code}

We can guarantee termination of |unfold| because the type |f| requires
it to show the clock has not run out of time in the |inr| case, so
that we can safely recurse on |s'|. Accepting unfold as terminating
would be challenging for a syntactic check, since the relationship
between |s'| and |s| depends on the semantics of |f|. In fact
unfolding a constant function |f| that always returns |inr (a , s')|
would never reach the base case. The |tribk| modality prevents such an
|f| because there's no way to always guarantee that the clock |k| has
remaining time left. The use
of |extract| is justified if we assume that |A| does not mention |k|.

We can make use of the |S| argument to acquire information about |k|
like in the following example. Using |unfold| and a type of bounded
natural numbers we define the function |downfrom|, which returns a
list counting down to $1$.
\begin{code}
Zero  : ∀ k . Nat uk
Suc   : ∀ k . tribk Nat uk -> Nat uk

downfrom : ∀ k . Nat uk → List (∃ k . Nat uk)
downfrom =
  unfold   (λ k n ->   case n of
                                         Zero    -> inl _
                                         Suc n'  -> inr ((pack(k)(n)) , n'))
\end{code}
The existential quantification allows us to forget the time
information of the naturals in the list, so that we do not have to keep
it synchronized with the clock |k| given to the function we unfold.

\subsection{Inductive types}
\label{sec:indty}
In previous work on guarded recursion, coinductive types were obtained
by universal clock quantification over their guarded variant, e.g. |∀
k . Stream uk Nat| would be the type of coinductive streams. In the
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
Suc uk : tribk Nat uk -> Nat uk
Suc uk   = λ n . inr n
\end{code}

Now we can bind the clock variable with an existential to define
\begin{code}
Nat = ∃ k . Nat uk
\end{code}
and show that |Nat| supports the expected iterator.

\begin{code}
fold : A -> (A -> A) -> Nat -> A
fold z f (pack k n) = fixb (\ k r n ->
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
specific clock they were built with, exactly like weak sums do, for the quantified type, in System
F. Intuitively Nat will not be the initial algebra of |(⊤ +)| unless |Nat ≅
⊤ + Nat| holds, so we must be able to support both an interface and an
equational theory where clocks play no role.

In the calculus we will internalize this invariance over the packaged
clock as type isomorphisms that we will justify with a parametric
model (Section \ref{sec:model}). In the specific case of |Nat|, both |(pack k (inl tt))| and
|(pack k' (inl tt))| get sent to |inl tt| by the isomorphism, so we can
conclude they are equal.

%% In other models of guarded recursion, |∀ k| or analogous modalities
%% are modeled by categorical limits, so it wasn't a stretch to imagine
%% |∃ k| as a colimit, however the trick for them to meaningfully coexist
%% is to be parametric limits and colimits, as in \cite{dunphyReddy:lics04}.

Once we scale up to a dependently typed language we will also be able
to implement an induction principle in terms of |fix| in Section
\ref{sec:induction}. However before that we will describe our
calculus, where we directly manipulate time values instead of clocks
to express programs more directly, rather than introducing additional combinators.

\mytodo{Maybe have an introduction subsection about the model too?}
\section{From Clocks to Time}
\label{sec:lang}
The notation we have used in the examples so far is closely modeled on
the one used in \cite{atkeyMcBride:icfp13} and \cite{mogelberg:csllics14}. In particular
clocks are a convenient abstraction over explicitly handling time values,
since we can use the same clock to refer to different amounts of time
depending on the context.

We can think of clock variables as indices into an environment of
values of type |Time|. This environment however is not passed untouched to every
sub-expression, or simply added to by binders, it also gets updated at the index |k| by
the modalities |tritk| and |tribk| for the scope of their
arguments.
So the same clock variable represents different time values in different parts of a type expression.
%% TODO example?
%% Stream uk A -> tritk (Stream uk A)
%%A good
%%analogy is Haskell's |Reader| monad: a clock variable looks up the current value in the
%%environment, while |tritk| and |tribk| locally override it with a smaller one.

To clarify the flow of |Time| we instead adopt a syntax inspired by Sized
Types \cite{abelPientka:icfp13}: we give the translation for types in Figure \ref{fig:translation}. This notation will also offer more flexibility in
the dependent case. In fact the first step is to add to the dependently
typed language of Figure \ref{fig:TT} a new type |Time|, together with inequality
|(i j : Time) ⊢ i ≤ j|, zero |0 : Time|, successor |↑ : Time -> Time| and a maximum operator |⊔ : Time -> Time -> Time|
(Figure \ref{fig:Time}).

The theory we will present does not support decidable typechecking and
includes some uniqueness principles that would not be suitable for an
intensional type theory like Coq and Agda. This theory is however
useful to present the properties of the denotational model of
Section~\ref{sec:model} and we consider it as a first step towards an
intensional theory with decidable typechecking.

Universal quantification over |Time| is simply done with a dependent
function type, and the |tritk| modality is a corresponding bounded
version. As a result the type |∀ k . tritk Nat uk| becomes |(i :
Time) -> (j : Time) -> ↑ j ≤ i -> Nat uj|, where the smaller time |j|
is explicitly mentioned and passed as the time parameter of the
guarded natural numbers type.

In the following we use the shorthand $∀ i .~A$ in place of $(i :
\Time) \to A$ and $∀ j < i .~A$ in place of $(j : \Time) \to~↑ j \leq i \to
A$, and so we also omit the inequality proof in abstractions and
applications, writing |λ j| in place of |λ j (p : ↑ j ≤ i)| and |f j|
in place of |f j p|.
\mytodo{We can then translate $\flater^\kappa\, A[\kappa]$ to $∀ j < i.~ [[A]][j]$ give full translation? explain [[.]]?}

As an example the operator |<*>| is given the following type and implementation:
\begin{code}
(<*>) :  ∀ i . (∀ j < i . A -> B)
         ->    (∀ j < i . A) -> (∀ j < i . B)
f <*>! x = λ j -> f j (x j)
\end{code}
Given a smaller time |j| we get the values of |f| and |x| at that time
and apply one to the other.

With this formulation it is also easy to see how to generalize |<*>|
to the dependent case since we can get hold of |j| and pass that to
|x| to obtain a valid argument for the dependent type |B|:
\begin{code}
(<*>>) :  ∀ i . (∀ j < i . (x : A) -> B x)
          ->    (x : ∀ j < i . A) -> (∀ j < i . B (x j))
f <*>>! x = λ j -> f j (x j)
\end{code}

However the existential quantification |∃ i. A| for |Time|, shown in Figure \ref{fig:exists},
has to be distinct from a plain |Σ| type because allowing an
unrestricted first projection would let us observe the specific |Time|
contained. The result type of the case expression for |∃ i . A| instead is restricted to belong to the universe |U|,
which lacks a code for |Time| itself (Figure \ref{fig:codes}).
We can specialize the case expression to the non-dependent case and implement an |uncurry| combinator:
\begin{code}
uncurry : (∀ i. A → El B) → (∃ i . A) → El B
uncurry f x = case x of (pack i a) -> f i a
\end{code}
where we can pattern match on |(pack i
a)| because the return type belongs to the universe |U|.
We also add a form of $\eta$ expansion for |∃ i|, which will be
necessary to ensure the proper computational behaviour for induction.
%%In the model we will see that |∃| is exactly a
%%"truncation" of the corresponding |Σ| to the universe |U|
%%(Section \ref{sec:model}).

Dually to |tritk| we have that |tribk| corresponds to a bounded |∃|
and we allow similar shorthands |∃ j < i. A| for |∃ j . ↑ j ≤ i ×
A| and |(pack j a)| for |(pack j (p , a))|.
As an example we show the implementation of |star|:
%%As an example we show the implementation of |star|, where the presence
%%of |El| on the return type ensures that we can the pattern match on |(pack j
%%x)|:
\begin{code}
(star) :  ∀ i . (∀ j < i . A -> El B)
          ->    (∃ j < i . A) -> El (∃ j < i . B)
f stari (pack j x) = (pack j (f j x))
\end{code}
We can also implement |extract| for |A : U|:
\begin{code}
extract : (A : U) -> ∀ i . (∃ j < i . El A) → El A
extract A i (pack j a) = a
\end{code}


The |fix| combinator, shown in Figure \ref{fig:fix}, is taken as a
primitive principle of well-founded induction on |Time|. The notation
|A[i]| stands for a type with |i| occurring free, so that |A[j]| has
instead all those occurrences replaced by |j|.
The equality rule for |fix f i| describes it as the unique function with this unfolding,
\begin{code}
fix f i = f i (guardt (fix f) i)
\end{code}
however such an equality, which is
justified by the model, leads to loss of normalization making typechecking undecidable.
We discuss possible solutions in Section \ref{sec:future}.

As anticipated in Section \ref{sec:indty} we internalize with
isomorphisms the properties of invariance with regard to |Time| of our
language. The isomorphisms of Figure \ref{fig:isos} describe how the
|Time| quantifiers commute with the other connectives and enrich the
equational theory.
We take as example the pair of |guardb| and |forceb|:
\begin{code}
guardb : (∃ i . A i) -> ∃ i . ∃ j < i. A j
guardb (pack i a) = (pack (↑ i) (pack i a))

forceb : (∃ i . ∃ j < i. A j) → ∃ i . A i
forceb (pack i (pack j a)) = (pack j a)
\end{code}
the $\beta$ and $\eta$ rules for |∃ i| are not enough to show that they are an isomorphism,
in particular they only allow us to conclude that
\begin{code}
guardb (forceb (pack i (pack j a))) = (pack (↑ j) (pack j a))
\end{code}
but having imposed that |guardb| and |forceb| form an isomorphism we can additionally deduce that
\begin{code}
(pack i (pack j a)) = (pack (↑ j) (pack j a))
\end{code}
showing that the packaged times |i| and |↑ j| are in fact irrelevant in that position.

In the case of |∀ i| we additionally have the usual isomorphisms that
can be implemented for dependent functions:

\begin{align*}
|∀ i. A × B |\, &|≅|\, |∀ i. A × ∀ i. B| \\
|∀ i. (x : A) → B|\, &|≅|\, |(x : A) → ∀ i . B| & i \not\in \mathsf{fv}(A)\\
|∀ i. ∀ j. A|\, &|≅|\, |∀ j. ∀ i. A|\\
\end{align*}

The limitation to only finite |El A| in the isomorphism
\begin{code}
∃ i . (x : El A) -> ∃ j < i. B ≅ (x : El A) → ∃ j . B
\end{code}
is because, to go from right to left, we need to find a |i| which is
an upper bound for all the |j|s returned by the function $(x : \El~A) \to
∃ j .~B$ across the whole domain $\El~A$. However given only |⊔| we can
only compute the upper bound of finitely many time values.  We did not
introduce a $\mathsf{limit} : (A \to \Time) \to \Time$ operator because |A| might
contain |Time| itself, and that would have led to impredicativity
issues in the model of Section \ref{sec:model}\mytodo{more like size issues?}. We plan to lift this
restriction in further work.

%include rules.lagda

%% -

\section{Inductive Types}
\label{sec:induction}

In this section we will show how to implement the recursive type
equations we have used in terms of fixed points on the universe, then
the induction principle for |Nat|, and lastly we construct an initial
algebra for any functor that properly commutes with |∃ i|.

\subsection{Recursive Type Equations}

For any function |F : U -> U| we can build |Fixb F : Time -> U| such
that |Fixb F i = F (∃ j < i. Fixb F j)|.

The first step is to recognize that |∃ j < i.| can take an element
of |∀ j < i. U| as input rather than |U| or |Time -> U|, defining
the combinator |wtribi|.
\begin{code}
wtribi : (∀ j < i. U) -> U
wtribi X = ∃ j < i. X j
\end{code}
Using the time analogy for intuition, in a case where we have no time
left, so there's no |j < i|, we already know that |∃ j < i. A|
is equivalent to |⊥| without having to know what |A| is, only if we
actually have time to spare we will look into it.

Given |wtribi| we can turn $F : \U \to \U$ into $∀ i .~(∀j < i.~\U) \to \U$ by
precomposition and define |Fixb| through |fix|, giving us the desired
property.
\begin{code}
Fixb = fix (λ i X . F (wtribi X))
\end{code}

In the same way we define |Fixt| by |wtriti|:
\begin{code}
wtriti : (∀ j < i. U) -> U
wtriti X = ∀ j < i. X j
\end{code}

\subsection{Induction on Nat}
To get a concrete feel for how we can reduce induction to |fix| we
show induction for the natural numbers.

First we redefine |Nat|, and show the definition of its constructors |Zero| and |Suc|:
\begin{code}
Nat = El (∃ i. Fixb (\ X . ⊤ + X) i)

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
          -> P Zero
          -> (∀ n -> El (P n) -> El (P (Suc n)))
          -> (n : Nat) -> El (P n)
indNat P z s (pack i n) =
  fix (\ i rec n ->  case n of
                       inl tt          -> z
                       inr (pack j n)  -> s (pack j n) (rec j n)
       )
      i n
\end{code}

Reading carefully we see that |s (pack j n) (rec j n)| has type |El (P
(Suc (pack j n)))| which we can reduce to $\El~(P~(↑ j, \mathsf{inr}~
(j, n)))$ while the expected type is |El (P (pack i (inr (pack j
n))))|.  We can however conclude that |(pack (↑ j) (inr (pack j n)))|
and |(pack i (inr (pack j n)))| are equal since they both get sent to
|(pack j n)| by the
\begin{code}
∃ i . ⊤ + (∃ j < i . A) ≅ ⊤ + ∃ i. A
\end{code}
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
such that |F₁| preserves identities and composition up to judgemental equality.

As an example we can make |∃ j < i.| into a |(Time × X)|-indexed
functor by defining |trib| like so:
\begin{code}
(trib)₀ : (Time × X → U) → (Time × X → U)
(trib)₀ A (i , x) = ∃ j < i . A (j , x)
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
mutri F (i , x) = fix (\ i A x . F (\ y. ∃ j < i . A (j , x)) i x
\end{code}
so that |mutri F = F[trib mutri F]|.

The algebra |F[trib mutri F] ⇒ mutri F| is then the identity.
We define the universal morphism from any other algebra |f : F[trib A] ⇒ A| through
|fix|.
\begin{code}
foldtri :  (A : Time × X → U) ->
           (F[trib A] ⇒ A) → mutri F ⇒ A
foldtri A f (i , x) = fix (\ i foldtri m. f (F (foldtri star) m)) i x
\end{code}
The uniqueness of |foldtri| follows from the rule Fix-Eq.

\subsection{Initial Algebras}

Initial algebras can then be obtained by |\ x → ∃ i. mutri F (i , x)|
for those |X|-indexed functors |F| which weakly commute with |∃ i| in the following sense.

%%% TODO use environment
\begin{definition}
Let |F| be an |X|-indexed functor, we say that |F|
weakly commutes with |∃ i| if the canonical map
\begin{code}
(x : X)  → (∃ i . F [trib A] (i , x))
         → F (\ x' → ∃ i. A (i , x')) x
\end{code}
is an isomomorphism for every |A|.
\end{definition}

%%% TODO use environment
%%Theorem 1.
\begin{theorem}
Let |F| be an |X|-indexed functor that weakly commutes with |∃
i|, then |mu F x = ∃ i. mutri F (i , x)| is the initial algebra of
|F|.
\end{theorem}
Proof (Sketch). From |F| weakly commuting with |∃ i| at type |mutri F| we
obtain an indexed isomorphism |F (mu F) ≅ mu F| and so in particular
an algebra |F (mu F) ⇒ F|, the morphism from any other algebra is
obtained from the one for |mutri| and inherits his uniqueness since
there's a bijection between algebra morphisms like in \cite{mogelberg:csllics14}.
\begin{code}
fold : (A : I → U) -> (F A ⇒ A) → (mu F ⇒ A)
fold A f x (pack i m) = foldtri (\ (i , x) → A x)
                                (λ j m → f (F extract m)) i x m
\end{code}

To determine whether a functor |F| weakly commutes with |∃ i| we make
use of the isomorphisms of Figure \ref{fig:isos}, in particular we can
handle the finitary-branching strictly positive functors but not
functors of the form
\begin{code}
F X = Nat -> X
\end{code}
or
\begin{code}
F X = Stream X
\end{code}
because of the limitations already discussed.

\subsection{(Guarded) Final Coalgebras}
The above result can be dualized to obtain final coalgebras of
|X|-indexed functors |F| that commute with |∀ i|.

For each |X|-indexed functor |F| we obtain the final coalgebra of
|F[trit -]| by
\begin{code}
nutri F (i , x) = fix (\ i A x. F (\ y. ∀ j < i . A (j , x)) i x
\end{code}
so that |nutri F = F[trit nutri F]|.

\begin{definition}
Let |F| be an |X|-indexed functor, we say that |F|
weakly commutes with |∀ i| if the canonical map
\begin{code}
(x : X)  → F (\ x'. ∀ i. A (i , x')) x
         → (∀ i . F [trit A] (i , x))
\end{code}
is an isomomorphism for every |A|.
\end{definition}

\begin{theorem}
Let |F| be an |X|-indexed functor that weakly commutes with |∀
i|, then |nu F x = ∀ i. nutri F (i , x)| is the final coalgebra of
|F|.
\end{theorem}

\mytodo{dependent elimination for |nu F| ?}
\subsection{Mixed Recursion-Corecursion}
Here we show with an example that the language can handle cases of
mixed recursion-corecursion by nested uses of |fix|.

From \cite{blanchettePopescuTraytel:icfp15} we take the example of a function
\begin{code}
cat : Nat -> Stream Nat
\end{code}
such that |cat 1| is the stream of Catalan numbers: $C_1,C_2,C_3,
\ldots$ where $C_n = \frac{1}{1 + n}\binom{2n}{n}$.
The function itself is of little interest other than being a concise
example of mixed recursion-corecursion.

We define |Stream A| as the final coalgebra of |A ×|, with |Stream ui
A| as the guarded version.
\begin{code}
Stream ui A = El (Fixt (\ X . A × X) i)
Stream A = ∀ i . Stream ui A
\end{code}
We also assume we have a function
\begin{code}
merge : ∀ i . Stream ui Nat -> Stream ui Nat -> Stream ui Nat
\end{code}
which sums the elements of two streams pointwise.

Given the above we nest two calls to |fix|, the outer one used for the
corecursive calls, while the inner one for the recursive one. The
order of the nesting makes so |catt| can accept an arbitrary natural
number as argument, while |catb| only one strictly bounded by |j|.
Conversely |catb| produces a stream bounded by |i| while |catt| only a
stream at a smaller bound.
\begin{code}
cat' : ∀ i → Nat → Stream ui Nat
cat' = fix (λ i catt . uncurry (fix (\ j catb n .
  case n of
    inl _   ->  Suc Zero , catt ast pure (Suc Zero)
    inr n'  ->  extract (catb starj n')
                merge (Zero , catt ast pure (Suc (pack j (inr n'))))
  )))

cat n = λ i . cat' i n
\end{code}

%% gcd example? https://github.com/pigworker/MGS14/blob/master/Lec4Crib.agda


\section{A Parametric Model}
\label{sec:model}

The type isomorphisms involving |∀ i| of Figure \ref{fig:isos} express
the intuition that values are constructed in a |Time| invariant way,
dually the isomorphisms involving |∃ i| express the intuition that the
only elimination principle for |∃ i| is |Time| invariant.
%% anything more precise than "express the intuition"?

Since \cite{Reynolds}, Relational Parametricity
\mytodo{caps?} has been shown to be a good tool to capture invariance
properties of programs, initially applied to invariance of polymorphic
types under change of data representation, but also invariance under
change of units of measure \cite{kennedy:units09} or manipulations of vectors
under translations \cite{atkeyJohannKennedy:popl13}. \mytodo{cite atkey 2014 ?}

The basic principle is that types get modeled as a pair of a set of
values and a relation over that set. The relation describes a property
that has to be preserved when manipulating such values.

To model our language then we make use of the relationally parametric model of
dependent type theory from \cite{atkeyGhaniJohann:popl14}, defining |Time| as the
type of natural numbers related by |<=| and the universe |U| as
small sets related by proof-irrelevant relations (their
``Small, Discrete, Proof Irrelevant Universe'').

\subsection{Reflexive Graphs as a Category with Families}
The model is formulated as a Category with Families \cite{dybjer:internalTypeTheory}, of
which we do not repeat the full definition but the main components are
\begin{itemize}
\item a category $\CxtF$ of semantic contexts
\item a collection $\TyF \Gamma$ of semantic types for each $\Gamma \in \Obj(\CxtF)$
\item a collection $\TmF \Gamma A$ of semantic terms, for each $A \in \TyF \Gamma$.
\end{itemize}
The category $\CxtF$ in our case is the functor category $\CSet^\RG$,
where $\RG$ is the small category with two objects, two parallel arrows, and a common section. Since
$\CxtF$ is a presheaf category it inherits a standard
Category with Families structure \cite{Hofmann} including definitions
for the standard connectives, most of them lifted pointwise from
\CSet. Here we will mention only enough to explain our own connectives.

An object $\Gamma$ of $\CxtF$ is best thought of as a triple $(\Gamma_O, \Gamma_R,
\Gamma_{\refl})$ where $\Gamma_O$ is a set of objects, $\Gamma_R$ is a binary
relation over $\Gamma_O$ and $\Gamma_{\refl}$ is a function witnessing the
reflexivity of $\Gamma_R$.
\[
\begin{array}{l l}
\Gamma_O & : Set \\
\Gamma_R & : \Gamma_O × \Gamma_O \to Set \\
\Gamma_{\refl} & : \forall \gamma \in \Gamma_O.\; \Gamma_R(\gamma,\gamma)\\
\end{array}
\]
We will refer to an element of $\Gamma_O$ as an environment.
Morphisms $f : \Gamma \to \Delta$ are then a pair of functions $f_o$
and $f_r$ which commute with reflexivity:
\begin{gather*}
f_o : \Gamma_O \to \Delta_O \\
f_r : \forall \gamma_0, \gamma_1 \in \Gamma.\; \Gamma_R(\gamma_0,\gamma_1) \to \Delta_R(f_o(\gamma_0), f_o(\gamma_1)) \\
\mbox{such that}~
\forall \gamma \in \Gamma_O.\; f_r (\Gamma_{\refl}(\gamma)) = \Delta_{\refl} (f_o(\gamma))
\end{gather*}
These morphisms should be thought of as substitutions, since they map
environments of the context $\Gamma$ into environments of $\Delta$. We
use the notations $A\{f\}$ and $M\{f\}$ to apply the substitution $f$
to the type $A$ and term $M$.

The collection $\TyF \Gamma$ of types then consists of families of reflexive
graphs: a semantic type $A \in \TyF \Gamma$ is also a triple $(A_O,A_R,A_{\refl})$
but each component is indexed by the corresponding one from $\Gamma$, allowing types to depend on values from the environment.
\begin{gather*}
A_O : \Gamma_O \to Set \\
A_R : \forall \gamma_0 , \gamma_1 \in \Gamma_O,\; \Gamma_R(\gamma_0,\gamma_1) \to A_O(\gamma_0) × A_O(\gamma_1) \to Set \\
A_{\refl} : \forall \gamma \in \Gamma_O,\; \forall a \in A_O(\gamma).\; A_R(\Gamma_{\refl}(\gamma),a,a)
\end{gather*}

The empty context $\epsilon \in \Obj(\CxtF)$ is defined as the
singleton reflexive graph $\epsilon = (\{*\},(λ \, \_ \, \_ \, . \, \{*\}),(λ \, \_ \, \_ \, . \, *))$.
As a consequence an element of $Ty(\epsilon)$ corresponds to an object of \CxtF.
We can also extend a context $\Gamma$ by a type $A \in \TyF \Gamma$ to
obtain another context $\Gamma.A$ by pairing up each component.
\begin{gather*}
\begin{array}{l c l}
(\Gamma.A)_O &=& \{ (\gamma,a) \mid \gamma \in \Gamma, a \in A_O(\gamma)\}\\
\multicolumn{3}{l}{(\Gamma.A)_R((\gamma_0,a_0),(\gamma_1,a_1))} \\
  &=& \{ (\gamma_r,a_r) \mid \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), a_r \in A_R(\gamma_r,a_0,a_1)\}\\
\end{array}
\end{gather*}
We then have a map $\tfst : \Gamma.A \to \Gamma$ which projects out the
first component and has the role of a weakening substitution.

A semantic term $M \in \TmF \Gamma A$ correponds in principle to a
map $\Gamma \to \Gamma.A$ such that $\tfst \circ M = id_\Gamma$. It is
however defined explicitly as a pair of the following components:
\begin{gather*}
M_o : \forall \gamma \in \Gamma_O, \; A_O(\gamma)\\
M_r : \forall \gamma_0, \gamma_1 \in \Gamma_O, \; \forall \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), \; A_R(\gamma_r,M_o(\gamma_0),M_o(\gamma_1)) \\
\mbox{such that}\\
\forall \gamma \in \Gamma_O, \; M_r (\Gamma_{\refl}(\gamma)) = A_{\refl}(\Gamma_{\refl}(\gamma),M_o (\gamma))\\
\end{gather*}


\subsection{A Small, Discrete, Proof Irrelevant Universe}

In order to recover standard parametricity results like the free
theorems from \cite{Wadler}, Atkey et. al\mytodo{proper citation?} define a universe $\U
\in \TyF \Gamma$ to connect the relations of the reflexive graphs to
the equality of their set of objects.
In particular for each $A \in \TmF \Gamma \U$ we get a type $\El~A \in
\TyF \Gamma$ such that $(\El~A)_R(\Gamma_{\refl}(\gamma))$
is the equality relation of $(\El~A)_O(\gamma)$, up to isomorphism.

Fixing a set-theoretic universe $\Univ$, we can define the following properties of reflexive graphs:
%%% TODO use environment
%% Section 4.2. "Definition" ought to be in bold. Also, in the definition
%% of U_R, why not just say that |R(a,b)| <= 1, instead of the
%% injectivity constraint?
\begin{definition}
A reflexive graph $A$ is:
\begin{itemize}
\item small if $A_O \in \Univ$ and for all $a_0, a_1 \in A_O$, $A_R(a_0,a_1) \in \Univ$
\item discrete if $A$ is isomorphic to a reflexive graph generated by a set, i.e. $A ≅ (X,=_X,\refl_{=_X})$ for some set $X$.
\item proof-irrelevant if, for all $a_0, a_1 \in A_O$, the map $A_R(a_0,a_1) \to \{*\}$ is injective.
\end{itemize}
\end{definition}
We are now ready to define $\U$ and $\El$:
\begin{gather*}
\begin{array}{l c l}
\multicolumn{3}{l}{\U \in \TyF \Gamma}\\
\U_O(\gamma) &=& \mbox{the set of small discrete reflexive graphs}\\
\U_R(\gamma_r)(A,B) &=& \{R : A_O \to B_O \to Set \mid\\
  &&\hphantom{\{}\forall a \in A_O, b \in B_O, R(a,b) \in \Univ,\\
  &&\hphantom{\{}\mbox{the map } R(a,b) \to \{*\}\mbox{ is injective } \}\\
\U_{\refl}(\gamma)(A) &=& A_R\\
\\
\multicolumn{3}{l}{\El \in \TyF {\Gamma.\U}}\\
\El_O(\gamma,A) &=& A_O\\
\El_R(\gamma_r,R) &=& R\\
\El_{\refl}(\gamma)(A) &=& A_{\refl}\\
\end{array}
\end{gather*}
Assuming that the set-theoretic universe $\Univ$ is closed under the corresponding operations,
the universe $\U$ is shown by \citep{atkeyGhaniJohann:popl14} to contain natural numbers
and to be closed under product and sum types, $\Sigma$ types and to contain $\Pi (x :
A).~\El~(B[x])$ for any small type $A$.


%% such that $(\El~A)_O$ is a family of
%% small sets, $(\El~A)_R$ is a family of proof irrelevant relations, and
%% for all $\gamma \in \Gamma_O$ we have that $(\El~A)_R(\Gamma_{\refl}(\gamma))$
%% is the equality relation of $(\El~A)_O(\gamma)$.Where the latter two requirements are to be considered up to isomorphism.

%% \subsubsection{Invariance through Discreteness}
%% \label{sec:inv-disc}

%% One main feature of $\U$ is exemplified by considering a term $M \in
%% \TmF{\Gamma.A}{(\El~B)\{\tfst\}}$, i.e., where the type of the result is in the universe
%% and does not depend on $A$.

%% \begin{lemma}
%% \label{lem:inv-disc}
%% Let $A \in \TyF \Gamma$, $B \in \TmF \Gamma \U$, and $M \in
%% \TmF{\Gamma.A}{(\El~B)\{\tfst\}}$ then
%% \begin{gather*}
%% \forall \gamma \in \Gamma_O, \;
%%       \forall a_0, a_1 \in A_O(\gamma), \;
%%       \forall a_r \in \A_R(\Gamma_{\refl}(\gamma),a_0,a_1), \; \\
%%         M_o(\gamma,a_0) = M_o(\gamma,a_1)
%% \end{gather*}
%% \end{lemma}
%% %% One main feature of $\U$ is exemplified by considering a term $M \in
%% %% \TmF{\Gamma.A}{(\El~B)\{\tfst\}}$ where $A \in \TyF \Gamma$ and $B \in
%% %% \TmF \Gamma \U$, i.e. where the type of the result is in the universe
%% %% and does not depend on $A$.
%% \begin{proof}
%% Unfolding the application of $\tfst$ and unpacking the environment for $\Gamma.A$ we get the following for the components of $M$:
%% \[
%% \begin{array}{l c l}
%% M_o &:& \forall \gamma \in \Gamma_O, \; \forall a \in A_O(\gamma), \; (\El~B)_O(\gamma) \\
%% M_r &:& \forall \gamma_0, \gamma_1 \in \Gamma_O, \;
%%       \forall \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), \; \\
%%       & &\forall a_0 \in A_O(\gamma_0), a_1 \in A_O(\gamma_1), \;
%%       \forall a_r \in A_R(\gamma_r,a_0,a_1), \; \\
%%        & &(\El~B)_R(\gamma_r, M_o(\gamma_0,a_0), M_o(\gamma_1,a_1))\\
%% \end{array}
%% \]
%% We see that the result of $M_r$ does not mention $a_r$ because $\El~B$ does not depend on $A$, moreover if
%% we specialize $\gamma_r$ to $\Gamma_{\refl}(\gamma)$ we get $(\El~
%% B)_R(\Gamma_{\refl}(\gamma), M_o(\gamma,a_0), M_o(\gamma,a_1))$, which we
%% know to be isomorphic to $M_o(\gamma,a_0) = M_o(\gamma,a_1)$ so we have our result.
%% \end{proof}

%% In other words, for a fixed $\gamma$, we have that $M_o$ considers any
%% two related $a_i$ as being equal, since it returns the same result.

%% Another important feature of $\U$ corresponds to Reynolds' identity
%% extension lemma. In fact a map like $T : \U \to \U$, which could
%% e.g. be a type constructor like |List|, has a relation component $T_r$
%% which is equality preserving, bla blah

\subsection{Interpretation of the Language}
We are left with having to interpret our own primitives.

\subsubsection{|Time|}

The type |Time| is intepreted as the reflexive graph of natural
numbers with the total relation. Assuming that $ℕ \in \Univ$ we
have that $\Time$ is small, but not discrete.
\begin{gather*}
\begin{array}{l c l}
\Time \in \TyF\epsilon\\
\Time_O &=& ℕ\\
\Time_R(n,m) &=& \{ * \}\\
\Time_{\refl}(n) &=& *\\
\end{array}
\end{gather*}
The terms for |0| and |↑| are implemented by $0$ and $+1$ on the underlying naturals, and |⊔| by taking the maximum.

Having $\Time_R$ relate any pair of values is how we encode the
invariance with respect to time that we want in the model as we show in Section~\ref{sec:isoproofs}.
%% In fact from Lemma \ref{lem:inv-disc} it follows that
%% that a term $M \in \TmF {\Gamma.\Time} {(\El~B)\{\tfst\}}$ is
%% going to produce the same result no matter what natural number it gets
%% from the environment, since they are all related, which justifies the isomorphism $∀ i. \El~
%% B ≅ \El~B$ of the language.\mytodo{mention that Pi types are naturally isomorphic to open terms?}

The relation between times |i ≤ j| is intepreted by\\ $\Le \,\, \in \TyF
{\Time.\Time\{\tfst\}}$, which also fits in $\U$ since it has no
interesting inhabitants.
\begin{gather*}
\begin{array}{l c l}
\Le_O(n , m) &=& \{ * \mid n \le m \} \\
\Le_R(\_,\_) &=& \{*\}\\
\Le_{\refl}(\_) &=& *
\end{array}
\end{gather*}

The fixpoint operator |fix| and its uniqueness are implemented through
well-founded induction on the natural numbers.
%%In particular given $f \in \TmF {\Gamma.Time.

\begin{definition}(∀ i) Let $\Gamma$ be a semantic context and $B \in \TmF {\Gamma.\Time} \U$ we define $∀ B = \Pi~\Time~B \in \TmF \Gamma \U$.
\end{definition}
\subsubsection{Representationally Independent Existential}

We will interpret the existential quantification over |Time|
in a way that corresponds to a parametric colimit in the sense of
\cite{dunphyReddy:lics04}. However we will show a connection with the standard $\Sigma$ type by
first defining a general operation to convert any small reflexive
graph into a discrete and proof-irrelevant one.

Given a small $A \in \TyF \Gamma$ we define $\Tr A \in \TmF \Gamma \U$
which we call the discrete truncation of $A$. On closed types $(\El
(\Tr A))_O$ is the colimit of $A$ as a diagram from $\RG$ and more
generally it will have the following universal property $\TmF
\Gamma {\El~(\Tr A) \to \El B} ≅ \TmF \Gamma {A \to \El B}$.

To give an explicit construction for $\Tr A$ we first present some
preliminary definitions on reflexive graphs and then lift those to the
case of families.

For a reflexive graph $A \in \Obj(\CxtF)$ we define $\rt A$ to be the
set obtained by quotienting $A_O$ with $A_R^\st$, which is how we denote the symmetric transitive closure of $A_R$.
\begin{gather*}
\rt A = A_O/(λ a_0~a_1.~ \exists \tilde{a}.~\tilde{a} \in A_R^\st(a_0,a_1))
\end{gather*}
Moreover we define $\LiftF_{(A,B)}(R)$ to lift a relation $R : A_O \to
B_O \to Set$ to a relation $\rt A \to \rt B \to Set$, so that we have
a function $\liftF_R : \forall a, b. \, R(a,b) →
\LiftF_{(A,B)}(R)([a],[b])$.
\begin{gather*}
\begin{array}{l c l}
\LiftF &:& \forall A, B \in \Obj(\CxtF), \forall (R : A_O \to B_O \to Set),\\
       & &  \rt A \to \rt B \to Set \\
\end{array}\\
\LiftF_{(A,B)}(R)([ a ],[ b ])\\
\begin{array}{l c l c l}
  &=& \{ (a',\tilde{a} ,b',\tilde{b},r) &\mid& a' \in A_O, \tilde{a} \in A_R^\st(a,a'),\\
  & & & &b' \in B_O, \tilde{b} \in B_R^\st(b,b'),\\
  & & & &r \in R(a',b') \}/\top\\
\end{array}
%% \LiftF_{(A,B)}(R : A_O \to B_O \to Set)(qa,qb) = \{ * \mid ∃ a. a \in [qa], ∃ b. b \in [qb], R(a,b) \} \\
%% \mbox{alternatively (by definition on the representatives)}\\
%% \LiftF_{(A,B)}(R : A_O \to B_O \to Set)([ a ],[ b ]) = \{ * \mid ∃ a'. A_R^\st(a,a'), ∃ b'. B_R^\st(b,b'), R(a',b') \} \\
\end{gather*}
The definition of $\LiftF_{(A,B)}(R)$ is given on the representatives
$a$ and $b$ of the equivalence classes $[a]$ and $[b]$, this is justified because we
produce logically equivalent relations for related elements.
We note that $\LiftF_{A,B}(R)$ is proof irrelevant by construction,
since we define it as a quotient with the total relation which we name $\top$,
and that $\LiftF_{(A,A)}(A_R)$ is logically equivalent to the equality relation on $\rt A$.

Finally we define $\Tr A$ for a given $A \in Ty(\Gamma)$:
\begin{gather*}
(\Tr A) : \TmF \Gamma \U\\
(\Tr A)_o(\gamma) = (A_O(\gamma)/^\st A_R(\Gamma_{\refl}(\gamma)),  \LiftF(A_R(\Gamma_{\refl}(\gamma)))) \\
(\Tr A)_r(\gamma_r) = \LiftF(A_R(\gamma_r))
\end{gather*}
we have to show that $(\Tr A)_o$ and $(\Tr A)_r$ commute with reflexivity,
\begin{gather*}
\forall \gamma, \U_{\refl}((\Tr A)_o(\gamma)) = (\Tr A)_r(\Gamma_{\refl}(\gamma))
\end{gather*}
but $\U_{\refl}$ projects out the relation given as the second
component of the tuple, so both sides reduce to
$\LiftF(A_r(\Gamma_{\refl}(\gamma)))$ and we are done.

We remark that, for any $A \in \TmF \Gamma \U$, the types $\El~A$ and $\El~(\Tr
A)$ are equivalent. In fact $A_r(\Gamma_{\refl}(\gamma))$ is already
equivalent to equality for $A_O(\gamma)$ so the quotient
$A_O(\gamma)/^\st A_r(\Gamma_{\refl}(\gamma))$ is equivalent to
$A_O(\gamma)$, and for the same reason $\LiftF(A_r(\gamma_r))$ is
equivalent to $A_r(\gamma_r)$.

The next step is to define an introduction and an eliminator for $\Tr
A$; the introduction sends an element of $A$ to its equivalence class:
\begin{gather*}
\begin{array}{l c l}
\multicolumn{3}{l}{\tr : \TmF {\Gamma.A} {\El~(\Tr A)\{\tfst\}}}  \\
\tr_o(\_,a)   &=& [ a ]\\
\tr_r(\_,a_r) &=& \liftF(a_r)
\end{array}
\end{gather*}
We then have dependent elimination of $\Tr A$ into other types $B \in
\TmF {\Gamma.\El~(\Tr A)} {\U}$ that live in the universe.
Given a $t \in \TmF {\Gamma.A} {\El~B\{⟨\tfst,\tr⟩\}}$ we define $\elim$:
\begin{gather*}
\begin{array}{l c l}
\multicolumn{3}{l}{\elim : \TmF {\Gamma.\El~(\Tr A)} {\El~B}}\\
\elim_o(\gamma,[ a ]) &=& t_o(\gamma,a)\\
\elim_r(\gamma_r, [ (a',\tilde{a},b',\tilde{b},r) ]) &=& t_r(\gamma_r,r)
\end{array}
\end{gather*}
Since $\elim_o$ and $\elim_r$ are defined by the representatives we
need to show they are invariant under the quotienting relation, also
$t_r(\gamma_r,r)$ is not immediately a member of the expected
relation, both of these problems are solved by the discreteness of
$B$.

%% This definition begs the questions of why we are allowed to work with
%% the representatives of these quotients and why $t_r(\gamma_r,r)$ is
%% even a member of the expected relation, both of these problems are
%% solved by the discreteness of $B$.

First we show that $t_r$ guarantees that $t_o$ respects $A_R(\Gamma_{\refl}(\gamma))$:
we unfold the type of $t_r$,
\[
\begin{array}{l c l}
t_r &:& \forall \gamma_0, \gamma_1 \in \Gamma_O, \; \gamma_r \in \Gamma_R(\gamma_0,\gamma_1), \;\\
    & & \forall a_0 \in A_O(\gamma_0), a_1 \in A_O(\gamma_1), a_r \in A_R(\gamma_r,a_0,a_1),\; \\
    & & (\El~B)_R((\gamma_r,\tr_r(a_r)), t_o(\gamma_0,a_0), t_o(\gamma_1,a_1))
\end{array}
\]
and note that for any $\gamma \in \Gamma_O$ we can take
$\gamma_r = \Gamma_{\refl}(\gamma)$ and obtain
\begin{gather*}
\forall a_0,a_1 \in A_O(\gamma), \; a_r \in A_R(\Gamma_{\refl}(\gamma),a_0,a_1), \\
(\El~B)_R((\Gamma_{\refl}(\gamma),\tr_r(a_r)), t_o(\gamma,a_0), t_o(\gamma,a_1)).
\end{gather*}
To use the discreteness of $(\El~B)$ we need the environment to be
obtained by reflexivity of $(\Gamma.\Tr A)$, so we need $\tr_r(a_r) =
(\Tr A)_{\refl}(a_0)$, and that follows from the proof-irrelevance of
$(\Tr A)_R$ and the fact that $\tr_o(a_0)$ equals $\tr_o(a_1)$.
Hence from discreteness $(\El
B)_R(\Gamma_{\refl}(\gamma),\tr_r(a_r))$ is equivalent to equality on
$(\El~B)_O(\gamma,\tr_o(a_0))$ and we can conclude:
\begin{gather}
\label{eq:respect}
\begin{array}{l}
\forall a_0,a_1 \in A_O(\gamma),\\ A_R(\Gamma_{\refl}(\gamma))(a_0,a_1) \to t_o(\gamma,a0) = t_o(\gamma,a_1)
\end{array}
\end{gather}
To justify the definition of $\elim_o$ we have to show that for two
$a_0, a_1 \in A_O(\gamma)$ related by $a_r \in
A_R(\Gamma_{\refl}(\gamma),a_0,a_1)$, we have $t_o(\gamma,a_0) =
t_o(\gamma,a_1)$; but this follows directly from the observation about $t_r$.

In the case of $\elim_r$ the proof-irrelevance of $(\El~B)_R$ already
implies that we will produce the same result for different
representatives, however it is less obvious that $t_r(\gamma_r,r)$
belongs in
\[ (\El~B)_R(\gamma_r,[
(a',\tilde{a},b',\tilde{b},r) ]), t_o(\gamma_0,a), t_o(\gamma_1,b)).
\]
We know that
\[ t_r(\gamma_r,r) \in (\El~B)_R(\gamma_r,\liftF(r)),
t_o(\gamma_0,a'), t_o(\gamma_1,b')) \]
and from \eqref{eq:respect} we know that
\[ t_o(\gamma_0,a) = t_o(\gamma_0,a')\] and
\[t_o(\gamma_1,b) = t_o(\gamma_1,b')\] so we also have \[ t_r(\gamma_r,r)
\in (\El~B)_R(\gamma_r,\liftF(r)), t_o(\gamma_0,a), t_o(\gamma_1,b))\]
and since $\liftF(r) = [ (a',\tilde{a},b',\tilde{b},r) ]$ by proof-irrelevance,
we obtain the result we wanted.


To define the existential we can then truncate the
corresponding $\Sigma$ type,
\[ ∃~A = \Tr~(\Sigma~\Time~A) \]
so that |(pack i a)| is interpreted as the introduction for $\Sigma$
followed by $\tr$, while the case expression is interpreted as $\elim$
combined with the projections of $\Sigma$.
More generally we could consider $∃~A~B = \Tr~(\Sigma A B)$. If both $A$ and $B$ belong in $\U$ then $∃~A~B$ is
equivalent to $\Sigma~A~B$, which reproduces the standard
result about recovering strong sums from weak ones by parametricity.

\subsubsection{Interpretation of the type isomorphisms}
\label{sec:isoproofs}
The validity in the model of the type isomorphisms from Figure
\ref{fig:isos} follows in most cases from the properties of $\Tr$.
In the following we write $A ≅_\Gamma B$ for $\TmF \Gamma A ≅ \TmF \Gamma B$.
\begin{lemma}
\label{lem:codisc}
Let $\Gamma$ be a semantic context, then $\El~(\Tr~\Time) ≅_\Gamma ⊤$.
\end{lemma}
\begin{proof}
Unfolding the definitions, $(\El~(\Tr~A))_O(\gamma)$ is the quotient of the
set of natural numbers by the total relation, hence it is a
singleton set.
\end{proof}

\begin{proposition}
  The isomorphisms from Figure \ref{fig:isos} are validated by the
  reflexive graph model.
\end{proposition}
\begin{proof}
  For reasons of space we only provide proofs for some of the
  isomorphisms, the others also similarly rely on the interaction
  between $\Tr$ and $\Time$.

  Let $\Gamma$ be a semantic context and $A \in \TyF \Gamma$ then we have the two following chains of isomorphisms:\\

  \noindent
  \setlength{\tabcolsep}{2pt}
  \begin{tabular}{lll}
  $\El~(∃~(A\{\tfst\}))$&$≅_\Gamma$& (by $\Sigma~\Time~(X\{\tfst\}) ≅_\Gamma \Time × X$)\\
  $\El~(\Tr~(\Time × \El~A)) $&$≅_\Gamma$& (by distributivity of $\Tr$ and $×$)\\
  $\El~(\Tr~\Time × \Tr~A) $&$≅_\Gamma$& (by Lemma \ref{lem:codisc})\\
  $\El~(⊤ × A) $&$≅_\Gamma$\\
  $\El~A$&\\
  \end{tabular}\\

  \noindent
  \begin{tabular}{lll}
  $\El~(∀~(A\{\tfst\}))$&$≅_\Gamma$&(by $\Pi~\Time~(X\{\tfst\}) ≅_\Gamma \Time \to X$)\\
  $\Time \to \El~A$&$≅_\Gamma$& (by the universal property of $\Tr$)\\
  $\El~(\Tr~\Time) \to \El~A$&$≅_\Gamma$& (by Lemma \ref{lem:codisc})\\
  $⊤ \to \El~A$&$≅_\Gamma$&\\
  $\El~A$\\
  \end{tabular}
  %% \vspace{20pt}
  %% \begin{tabular}{lll}
  %% $(∃ i.~A[i]) × (∃ i.~B[i])$&$≅$&\\
  %% $∃ j_A.~∃ j_B.~⊤ × A[j_A] × B[j_B]$&$≅$& (by Lemma \ref{lem:codisc})\\
  %% \multicolumn{3}{l}{$∃ j_A.~∃ j_B.~(∃ i.~ j_A < i × j_B < i) × A[j_A] × B[j_B] ≅$}\\
  %% $∃ i.~(∃ j.~j < i × A[j]) × (∃ j.~j < i × B[j])$\\
  %% \end{tabular}
\end{proof}
%% It is easy then to justify the isomorphism $∃ i . A ≅ A$ for an $A$
%% that doesn't mention $i$: the equality on $\Tr (\Sigma i : \Time.~A)$
%% ignores the $\Time$ fields because any two time values are related in
%% some direction.

\section{Related Works}

The application of Nakano's guard modality \cite{nakano:lics00} to coinductive types
started with \cite{atkeyMcBride:icfp13} by the introduction of clock
variables to an otherwise simply typed language, \cite{mogelberg:csllics14}
extended this result to a dependently typed setting where guarded
recursive types are constructed via fixed points on universes.
Their models are based on the topos of trees: a context with a
free clock variable is interpreted as a functor $\CSet^{\omega^{op}}$
where $\omega$ is the preorder of natural numbers as a category.
In such a model every value available at present time can be
transported to a later time by forgetting some of the contained
information, e.g. guarded streams of natural numbers correspond to the functor
\[
\mathsf{Stream}(n) = ℕ^{n+1}
\]
where the action on morphisms, so-called restriction map, sends $\mathsf{Stream}(n+1)$ to
$\mathsf{Stream}(n)$ by discarding the last element. %% TODO last element? restriction map?
Our |trib| modality however would not fit in such a model because
there is no map $(\trib A)(1) \to (\trib A)(0)$ in general: $(\trib
A)(0)$ is an empty set, since there are no future times, while
$(\trib A)(1)$ is only empty when $A(0)$ is.
We are then forced to give up these maps, but having
only $A : \CSet^{\mid\omega\mid}$ i.e., a collection of sets indexed by
natural numbers, would not be enough, in the parametric model the associated
relation is used to impose the invariance conditions needed.
However we lose the full applicative functor structure of $\trit$,
i.e. we lack
\begin{code}
pure  : ∀ i . (A i → ∀ j < i. A j)
\end{code}
for arbitrary types |A| and |B|. This is also the case for the system
in \cite{krishnaswami:icfp13} where the Nakano modality is used to control the
resource usage of funtional reactive programs. The lack of |pure| does
not seem to cause expressivity problems with regard to the examples in \cite{atkeyMcBride:icfp13}, and |pure| can be
implemented explicitly for those types that would support restriction
maps.

The notation we use for the |trit| and |trib| modalities agrees with
their use in provability logic and its Kripke
models. Unfortunately we conflict with other works on guarded
recursive types where $\trit$ is used as a nameless |∀ i| \cite{krishnaswami:icfp13,cloustonBizjakGrathwohlBirkedal:fossacs15}.

In HOL the system of tactics presented in \cite{blanchettePopescuTraytel:icfp15} allows
corecursive calls to appear under ``well-behaved'' corecursive
functions, which consume as much of their coinductive inputs as they
produce, i.e. that in our system would preserve the time values.
They do not consider more complex relations between inputs and outputs
and the well-behavedness of a function is not part of its type, so the
user interface is simpler, even if less expressive.

\subsection{Comparison to Sized Types}
When extended with copatterns \cite{abelPientka:icfp13}, Sized Types also justify
the totality of (co)recursive definitions by well-founded induction on
what there is called |Size|. The calculus presented there is defined
as an extension of System F-omega so equality of terms does not affect
typing. However, Abel and Pientka specify a strong normalizing reduction semantics while we have only specified equalities.
The calculus allows direct recursion, with which we can define a
general fixed point combinator
\begin{code}
fixlt :  ∀ (A : Size -> *). (∀ i. (∀ j < i. A j) -> A i)
         → ∀ i. ∀ j < i. A j
fixlt A f i j = f j (fixlt A f j)

fix :  ∀ (A : Size -> *). (∀ i. (∀ j < i. A j) -> A i)
       → ∀ i. A i
fix A f i = f i (fixlt A f i)
\end{code}
We have that |fix A f i| reduces to |f j (fixlt A f j)| which does not
reduce further unless |f| does. Because of this, reduction alone does
not validate the equality |fix f i = f (fix f)| of our language, which
instead would lead to the loss of strong normalization.
This fixed point operator cannot be used to define recursive types
since the calculus does not allow programs to compute types.
Instead there are explicit $\mu$ and $\nu$ type formers for inductive
and coinductive types. The calculus can handle arbitrary branching inductive
types thanks to a model where |Size| is interpreted as the set of
ordinal numbers.
Sized Types have also been experimentally added to Agda and have been
useful to allow more general patterns of recursion \cite{abelChapman:msfp14},
however the current definitional equality of Agda does not validate
the isomorphisms from our language, so the problem of values that
should be equal but differ only in |Size| values is still present.

Another important distinction is that Abel and Pientka aim for a judgemental equality that includes the
the equations the user writes, because of this they include extra
restrictions on when it is allowed to have a lambda abstraction over
sizes, e.g., defining a second fixed-point combinator like the following
\begin{code}
fix' :  ∀ (A : Size -> *). (∀ i. (∀ j < i. A j) -> A i)
       → ∀ i. A i
fix' A f i = f i (λ j. fix A f j)
\end{code}
would not be accepted as a definition, the typing rule for the
abstraction over $j < i$ checks whether it is already known that $i$ is
non-zero, and here that's not the case. This restriction ensures that
evaluation, even when going under lambdas, never assumes more about
the sizes in the context than what was already known, so the
well-foundedness of the order on sizes can be used to show termination.

Our work instead does not impose additional restrictions on lambda
abstractions involving sizes, so that the user can trust her
intuition of well-founded induction to know whether an expression will
be accepted. The rewriting semantics will need to cope
with this by using a different strategy to block evaluation.
%% too up in the air?
%comparison to sacchini or other guys?

%sized types
%- dependent type theory
%- fixpoint on universe instead of mu/nu style recursive types, but close enough for our mu/nu
%- no term reduction semantics, while sized types have WYSIWYG equations
%- invariance over time not formalized as equational rules
%- fix operator implementable.
%    - still terminating reduction behaviour, promising, but eta?
%- no infinity/subtyping
%- handle arbitrary branching types
%  - semantics use ordinals

%foundational coinduction

%conor/rasmus/neel
% - we have guarded inductive types!
% - tritk is no longer a strong functor..
%   - not a strong functor in neel's work either!
% - conor/rasmus model based on functor category Set^omega, but tribk doesn't fit.
%   - We could move to Set^|omega| but then ∀ k. just a product, no way to express invariance guarantees.
%   - so parametricity
% shulman/schreiber
% Tr is the shape/Π modality?
%
% provability logic

%% \mytodo{when comparing with guarded recursive types, say that to
%% internalize the functoriality "sized types" style you'd "need"? directed
%% type theory, which is a good technical reason to use clocks instead}

\section{Conclusions and Further Work}
\label{sec:future}
We have presented a model for a dependently typed calculus which
ensures the totality of both recursive and corecursive definitions in
a modular way through typing. Recursive types are also reduced to
well-founded recursion on |Time| and we have specified as isomorphisms
the invariance properties needed to obtain the expected equational
theory of inductive and coinductive types.
We have left open the issue of handling infinitely-branching inductive
types, because as explained in Section \ref{sec:lang} we would need a
|limit| operator for |Time|. We plan to investigate the meta-theoretic
consequences of extending the theory with such a |limit| operator and
modeling |Time| with a set of ordinals.\mytodo{can you have a set of ordinals?}
Such an extension would allow us to embed a universe for dependent
type theory as an inductive datatype, since we can encode
induction-recursion as a fixed point of families of types, so the
resulting theory would have a large\mytodo{big?} proof-theoretic
strength.
\mytodo{maybe this should be its own section with more details? we also need an additional universe}
We also want to formulate a strongly normalizing reduction semantics
for our language, extending the result for Sized Types to our theory,
in addition to formulating a decidable subset of the equational theory presented.



%% handle arbitrary branching trees
%%  - show that for F X = (A -> X) you need a "limit" operation on times
%%  - in particular A can contain ordinals, so need a powerful limit there.
%%  - have a "limit" for Time, use ordinals?
%%     - only need well-founded induction on Time, so situation similar to Coq's Prop
%%  - we will have induction-recursion by taking the fixpoint of families, so strong theory
%% terminating reduction semantics
%% - weaker definitional equalities for fix, but added back as propositional ones? i.e. adding an observational equality to sized types
%% handle invariance/irrelevance more explicitly
%% - modalities for parametricity? explicit intersection quantifier?
%% - equality rules anyway
%% - CC* Barras/Extending reflexive graphs model to a cubical one..
%% handle more universes


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

%% \acks
%% For discussions on dependent type theory, totality and denotational models I would like to thank Andreas Abel
% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\bibliography{auto-paper,icfp}

\end{document}

%                       Revision History
%                       -------- -------
%  Date         Person  Ver.    Change
%  ----         ------  ----    ------

%  2013.06.29   TU      0.1--4  comments on permission/copyright notices
