\documentclass{tmr}

%include polycode.fmt

%if style == poly
%format :+: = "\oplus"
%format :<: = "\hookrightarrow"
%format not = "not"
%format phi = "\phi"
%format phi1 = "\phi_1"
%format phi2 = "\phi_2"
%format ts   = "\bar t"
%format `O`  = "\bullet"
%endif

\title{First-Order Logic \`a la Carte}
\author{Kenneth Knowles\email{kknowles@@cs.ucsc.edu}}

\long\def\ignore#1{}
\setlength{\blanklineskip}{3mm}

\begin{document}

\begin{introduction} Classical first-order logic has the pleasant
property that a formula can be reduced to an elegant \emph{implicative
normal form} through a series of syntactic simplifications.  Using
these transformations as a vehicle, this article demonstrates how to
use Haskell's type system, specifically a variation on Swierstra's
``Data Types \`a la Carte'' method, to enforce the structural
correctness property that these constructors are, in fact, eliminated by
each stage of the transformation.  \end{introduction}

\begin{figure}[p]
\begin{code}
{-# LANGUAGE RankNTypes,TypeOperators,PatternSignatures #-}
{-# LANGUAGE UndecidableInstances,IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses,TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts,FlexibleInstances #-}

import Text.PrettyPrint.HughesPJ 
import Control.Monad.State
import Prelude hiding (or,and,not)
\end{code}
\caption{LANGUAGE pragma and module imports}
\end{figure}

\section{First-Order Logic}

Consider the optimistic statement ``Every person has a heart.''
If we were asked to write this formally in a logic or philosophy class, we might write the
following formula of classical first-order logic:

\[ \forall p.\, Person(p) \Rightarrow \exists h.\, Heart(h) \wedge Has(p,h) \\ \]

If asked to write the same property for testing by QuickCheck~\cite{quickcheck},
we might instead produce this code:

%if style == poly
\begin{code}
  heartFact :: Person -> Bool
  heartFact p = has p (heart p)
     where heart :: Person -> Heart
           ...
\end{code}
%endif

These look rather different.  Ignoring how some of the predicates
moved into our types, there are two other transformations involved.
First, the universally quantified $p$ has been made a parameter,
essentially making it a free variable of the formula.  Second, the
existentially quantified $h$ has been replaced by a function |heart|
that, for any person, returns their heart.  How did we know to encode
things this way?  We have performed first-order quantifier elimination
in our heads!

This idea has an elegant instantiation for classical first-order logic
which (along with some other simple transformations) yields a useful
normal form for any formula.  This article is a tour of the
normalization process, implemented in Haskell, using a number of
Haskell programming tricks.  We will begin with just a couple of
formal definitions, but quickly move on to ``all code, all the time.''

First, we need the
primitive set of terms $t$, which are either variables $x$ or function
symbols $f$ applied to a list of terms
(constants are functions of zero arguments).
\begin{eqnarray*}
  t & ::= & x  ~\mid~ f(t_1, \cdots, t_n)
\end{eqnarray*}

Next, we add atomic predicates $P$ over terms, and the logical
constructions to combine atomic predicates.  Since we are talking
about classical logic, many constructs have duals, so they are
presented side-by-side.  \[ \begin{array}{rclcl} \phi & ::= & P(t_1,
\cdots, t_n) \\ & \mid & \neg\phi \\ & \mid & \phi_1 \Rightarrow
\phi_2 \\ & \mid & TT & \mid & FF \\ & \mid & \phi_1 \wedge \phi_2 &
\mid & \phi_1 \vee \phi_2 \\ & \mid & \forall x.\, \phi & \mid &
\exists x.\, \phi \end{array} \]

We will successively convert a closed (no free variables) first-order
logic formula into a series of equivalent formulae, eliminating many of the above
constructs.  Eventually the result will be in \emph{implicative normal
form}, in which the placement of all the logical connectives is
strictly dictated, such that it does not even require a recursive
specification.  Specifically, an implicative normal form is the
conjunction of a set of implications, each of which has a conjunction
of terms on the left and a disjunction of terms on the right:

\[ implicative~normal~f\!orm ~ ::= ~ \bigwedge \left[\bigwedge t^* \Rightarrow \bigvee t ^*\right]^* \] 

The normal form may be very large compared to the input formula, but
it is convenient for many purposes, such as using Prolog's resolution
procedure or an SMT (Satisfiability Modulo Theories) solver. The
following process for normalizing a formula is described by Russell
and Norvig \cite{Russell2003} in seven steps:

\begin{enumerate}
\item Eliminate implications.
\item Move negations inwards.
\item Standardize variable names.
\item Eliminate existential quantification, reaching Skolem normal form.
\item Eliminate universal quantification, reaching prenex formal form.
\item Distribute boolean connectives, reaching conjunctive normal form.
\item Gather negated atoms, reaching implicative normal form.
\end{enumerate}

Keeping in mind the pattern of systematically simplifying the syntax
of a formula, let us consider some Haskell data structures for
representing first-order logic.

\subsection{A Natural Encoding}

Experienced Haskellers may translate the above definitions into
the following Haskell data types immediately upon reading them:

\begin{code}
data Term  =  Const String [Term]
           |  Var String
\end{code}

We will reuse the constructor names from |FOL| later, though, so this is
not part of the code for the demonstration.

%if style == poly
\begin{code}
data FOL  =  Impl FOL FOL
          |  Atom String [Term]  | Not FOL
          |  TT                  | FF 
          |  Or FOL FOL          | And FOL FOL
          |  Exists String FOL   | Forall String FOL
\end{code}
%endif

To make things more interesting, let us work with
the formula representing the statement
``If there is a person that eats every food, then there
is no food that noone eats.''

\[ 
\begin{array}{ll}
   & \exists p.\, Person(p) \wedge \forall f.\, Food(f) \Rightarrow Eats(p, f) \\
   \Rightarrow & \neg \exists f.\, Food(f) \wedge \neg \exists p.\, Person(p) \wedge Eats(p, f)
\end{array}
\]

%if style == poly
\begin{code}
foodFact = 
  (Impl 
    (Exists "p"
      (And  (Atom "Person" [Var "p"])
            (Forall "f"
              (Impl  (Atom "Food" [Var "f"])
                     (Atom "Eats" [Var "p", Var "f"])))))
    (Not (Exists "f"
           (And  (Atom "Food" [Var "f"])
                 (Not (Exists "p"
                        (And  (Atom "Person" [Var "p"])
                              (Atom "Eats" [Var "f"]))))))))
\end{code}
%endif

\subsection{Higher-Order Abstract Syntax}

While the above encoding is natural to write down, it has
drawbacks for actual work.  The first thing to
notice is that we are using the |String| type to represent
variables, and may have to carefully manage scoping.
But what do variables range over?  Terms.
And Haskell already has variables that range
over the data type |Term|, so we can re-use Haskell's implementation; 
this technique is known as higher-order abstract syntax (HOAS).

%if style == poly
\begin{code}
data FOL  =  Impl FOL FOL
          |  Atom String [Term]    | Not FOL
          |  TT                    | FF 
          |  Or  FOL FOL           | And FOL FOL
          |  Exists (Term -> FOL)  | Forall (Term -> FOL)
\end{code}
%endif

In a HOAS encoding, the binder of the object language 
(the quantifiers of first-order logic) are implemented
using the binders of the metalanguage (Haskell).  For
example, where in the previous encoding we would
represent $\exists x.\, P(x)$ as |Exists "x" (Const "P" [Var "x"])|
we now represent it with |Exists (\x -> (Const "P" [x]))|.
And our example becomes:

%if style == poly
\begin{code}
foodFact = 
  (Impl 
    (Exists $ \p ->
      (And  (Atom "Person" [p])
            (Forall $ \f ->
              (Impl  (Atom "Food" [f])
                     (Atom "Eats" [p, f])))))
    (Not (Exists $ \f ->
      (And  (Atom "Food" [f])
            (Not (Exists $ \p ->
                   (And  (Atom "Person" [p])
                         (Atom "Eats" [f]))))))))
\end{code}
%endif

Since the variables |p| and |f| have taken the place of the |String|
variable names, Haskell's binding structure now ensures that we cannot
construct a first-order logic formula with unbound variables, unless
we use the |Var| constructor, which is still present because we will need
it later.  Another important benefit is that the type now expresses
that the variables range over the |Term| data type, while before it
was up to us to properly interpret the |String| variable names.

\begin{exercise}
  Modify the code of this article so that the |Var|
  constructor is not introduced until it
  is required in stage 5.
\end{exercise}

\subsection{Data Types \`a la Carte}

But even using this improved encoding, all our transformations will be
of type |FOL -> FOL|.  Because this type does not express the
structure of the computation very precisely, we must rely on human
inspection to ensure that each stage is written correctly.  More
importantly, we are not making manifest the requirement of certain
stages that the prior stages' transformations have been performed.
For example, our elimination of universal quantification is only a
correct transformation when existentials have already been eliminated.
A good goal for refining our type structure is to describe our data
with types that reflect which connectives may be present.

Swierstra proposes a technique~\cite{dtalc} whereby a variant data type
is built up by mixing and matching constructors of different
functors using their \emph{coproduct} |(:+:)|, which is the
``smallest'' functor containing both of its arguments.

\begin{code}
data (f :+: g) a = Inl (f a) | Inr (g a)
infixr 6 :+:

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr x) = Inr (fmap f x)
\end{code}

The |:+:| constructor is like |Either| but it operates on functors.
This difference is crucial -- if |f| and |g| represent two
constructors that we wish to combine into a larger \emph{recursive}
data type, then the type parameter |a| represents the type of their
subformulae.

To work conveniently with coproducts, we define a type class |:<:| that implements subtyping by
explicitly providing an injection from one of the constructors to the
larger coproduct data type.  There are some technical aspects to
making sure current Haskell implementations can figure out the needed
instances of |:<:|, but in this example we need only Swierstra's
original subsumption instances, found in Figure \ref{fig:Subsumption}.
For your own use of the technique, discussion on Phil Wadler's
blog~\cite{wadler-dtalc} and the Haskell-Cafe mailing
list~\cite{haskell-cafe-dtalc} may be helpful.

\begin{figure}
\begin{code}
class (Functor sub, Functor sup) => sub :<: sup where
     inj :: sub a -> sup a

instance Functor f => (:<:) f f where
     inj = id

instance (Functor f, Functor g) => (:<:) f (f :+: g) where 
     inj = Inl

instance (Functor f, Functor g, Functor h, (f :<: g)) 
   => (:<:) f (h :+: g) where 
     inj = Inr . inj
\end{code}
\caption{Subsumption instances}
\label{fig:Subsumption}
\end{figure}

If the above seems a bit abstract or confusing, it will become very
clear when we put it into practice.  Let us immediately do so by
encoding the constructors of first-order logic in this modular
fashion.

\begin{code}
data TT      a  = TT
data FF      a  = FF
data Atom    a  = Atom String [Term]
data Not     a  = Not a
data Or      a  = Or a a
data And     a  = And a a
data Impl    a  = Impl a a
data Exists  a  = Exists (Term -> a)
data Forall  a  = Forall (Term -> a)
\end{code}

Each constructor is parameterized by a type |a| of subformulae;
|TT|, |FF|, and |Atom| do not have any subformulae so they ignore
their parameter. Logical operations such as |And| have two
subformulae. Correspondingly, the |And| constructor takes two
arguments of type |a|. 

The compound functor |Input| is now the specification of which
constructors may appear in a first-order logic formula.
\begin{code}
type Input =  TT :+: FF :+: Atom 
              :+: Not :+: Or :+: And :+: Impl 
              :+: Exists :+: Forall
  
\end{code}
The final step is to ``tie the knot'' with the
following |Formula| data type, which generates a recursive formula
over whatever constructors are present in its functor argument |f|.

\begin{code}
data Formula f = In { out :: f (Formula f) } 
\end{code}

If you have not seen this trick before, that definition may be hard to
read and understand.
Consider the types of |In| and |out|.
%if style == poly
\begin{code}
In   ::  f (Formula f) -> Formula f
out  ::  Formula f -> f (Formula f)
\end{code}
%endif
Observe that $|In . out == out . In == id|$.  This pair of inverses
allows us to ``roll'' and ``unroll'' one layer of a formula in order
to operate on the outermost constructor.  Haskell does this same thing
when you pattern-match against ``normal'' recursive data types.  Like
Haskell, we want to hide this rolling and unrolling.  To hide the
rolling, we define some helper constructors, found in Figure
\ref{fig:FOLboilerplate}, that inject a constructor
into an arbitrary supertype, and then apply |In| to yield a |Formula|.

To hide the unrolling, we use the fact that a fixpoint of a functor
comes with a fold operation, or \emph{catamorphism}, which we will use
to traverse a formula's syntax. The function |foldFormula| takes as a
parameter an \emph{algebra} of the functor |f|.  Intuitively,
|algebra| tells us how to fold ``one layer'' of a formula, assuming
all subformulae have already been processed.  The fixpoint then
provides the recursive structure of the computation once and for all.

\begin{code}
foldFormula :: Functor f => (f a -> a) -> Formula f -> a
foldFormula algebra = algebra . fmap (foldFormula algebra) . out
\end{code}

We are already reaping some of the benefit of our ``\`a la carte''
technique: The boilerplate |Functor| instances in Figure
\ref{fig:FOLboilerplate} are not much larger than the code of
|foldFormula| would have been, and they are defined modularly!  Unlike a
monolithic |foldFormula| implementation, this one function will work
no matter which constructors are present.  If the definition of
|foldFormula| is unfamiliar, it is worth imagining a |Formula f|
flowing through the three stages: First, |out| unrolls the formula one
layer, then |fmap| recursively folds over all the
subformulae. Finally, the results of the recursion are combined by
|algebra|.

\begin{figure}[p]
\begin{code}
instance Functor TT      where fmap _ _                 = TT
instance Functor FF      where fmap _ _                 = FF
instance Functor Atom    where fmap _ (Atom p ts)       = Atom p ts
instance Functor Not     where fmap f (Not phi)         = Not (f phi)
instance Functor Or      where fmap f (Or phi1 phi2)    = Or (f phi1) (f phi2)
instance Functor And     where fmap f (And phi1 phi2)   = And (f phi1) (f phi2)
instance Functor Impl    where fmap f (Impl phi1 phi2)  = Impl (f phi1) (f phi2)
instance Functor Forall  where fmap f (Forall phi)      = Forall (f . phi)
instance Functor Exists  where fmap f (Exists phi)      = Exists (f . phi)

inject :: (g :<: f) => g (Formula f) -> Formula f
inject = In . inj

tt :: (TT :<: f) => Formula f
tt = inject TT

ff :: (FF :<: f) => Formula f
ff = inject FF

atom :: (Atom :<: f) => String -> [Term] -> Formula f
atom p ts = inject (Atom p ts)

not :: (Not :<: f) => Formula f -> Formula f
not = inject . Not

or :: (Or :<: f) => Formula f -> Formula f -> Formula f
or phi1 phi2 = inject (Or phi1 phi2)

and :: (And :<: f) => Formula f -> Formula f -> Formula f
and phi1 phi2 = inject (And phi1 phi2)

impl :: (Impl :<: f) => Formula f -> Formula f -> Formula f
impl phi1 phi2 = inject (Impl phi1 phi2)

forall :: (Forall :<: f) => (Term -> Formula f) -> Formula f
forall = inject . Forall

exists :: (Exists :<: f) => (Term -> Formula f) -> Formula f
exists = inject . Exists
\end{code}
\caption{Boilerplate for First-Order Logic Constructors}
\label{fig:FOLboilerplate}
\end{figure}

Here is what our running example looks like with this encoding:

\begin{code}
foodFact :: Formula Input
foodFact =  (exists $  \p  -> atom "Person" [p]
                 `and` (forall $ \f  -> atom "Food" [f]
                                     `impl` atom "Eats" [p,f]))
  `impl`
  (not (exists $ \f  -> atom "Food" [f]
                     `and` (not (exists $ \p  -> atom "Person" [p]
                                              `and` atom "Eats" [p,f]))))
\end{code}

A TeX pretty-printer is included as an appendix to this article.  To
make things readable, though, I'll doctor its output into a nice
table, and remove extraneous parentheses.  But I won't rewrite the
variable names, since variables and binding are a key aspect of
managing formulae.  By convention, the printer uses $c$ for
existentially quantified variables and $x$ for universally quantified
variables.

\begin{verbatim}
*Main> texprint foodFact
\end{verbatim}

\[ 
\begin{array}{ll}
   & (\exists c_1.\, Person(c_1) \wedge \forall x_2.\, Food(x_2) \Rightarrow Eats(c_1, x_2)) \\
   \Rightarrow & \neg\exists c_4.\, Food(c_4) \wedge \neg\exists c_8.\, Eats(c_8, c_4)
\end{array}
\]

\section{Stage 1 -- Eliminate Implications}

The first transformation is an easy one, in which
we ``desugar'' $\phi_1 \Rightarrow \phi_2$ into $\neg \phi_1 \vee \phi_2$.
The high-level overview is given by the type and body
of |elimImp|.

\begin{code}
type Stage1 = TT :+: FF :+: Atom :+: Not :+: Or :+: And :+: Exists :+: Forall

elimImp :: Formula Input -> Formula Stage1
elimImp = foldFormula elimImpAlg
\end{code}

We take a formula containing all the constructors of first-order logic,
and return a formula built without use of |Impl|.  The way that
|elimImp| does this is by folding the algebras |elimImpAlg| for each
constructor over the recursive structure of a formula.

The function |elimImpAlg| we provide by making each constructor an
instance of the |ElimImp| type class.  This class specifies for a
given constructor how to eliminate implications -- for most
constructors this is just the identity function, though we must
rebuild an identical term to alter its type.  Perhaps there is a way
to use generic programming to eliminate the uninteresting cases.

\begin{code}
class Functor f => ElimImp f where
  elimImpAlg :: f (Formula Stage1) -> Formula Stage1

instance ElimImp Impl where elimImpAlg (Impl phi1 phi2)  = (not phi1) `or` phi2

instance ElimImp TT      where elimImpAlg TT                = tt
instance ElimImp FF      where elimImpAlg FF                = ff
instance ElimImp Atom    where elimImpAlg (Atom p ts)       = atom p ts
instance ElimImp Not     where elimImpAlg (Not phi)         = not phi
instance ElimImp Or      where elimImpAlg (Or phi1 phi2)    = phi1 `or` phi2
instance ElimImp And     where elimImpAlg (And phi1 phi2)   = phi1 `and` phi2
instance ElimImp Exists  where elimImpAlg (Exists phi)      = exists phi
instance ElimImp Forall  where elimImpAlg (Forall phi)      = forall phi
\end{code}

We extend |ElimImp| in the natural way over coproducts, so that whenever
all our constructors are members of the type class, then their coproduct is
as well.

\begin{code}
instance (ElimImp f, ElimImp g) => ElimImp (f :+: g) where
  elimImpAlg (Inr phi) = elimImpAlg phi
  elimImpAlg (Inl phi) = elimImpAlg phi
\end{code}

Our running example is now

\begin{verbatim}
*Main> texprint . elimImp $ foodFact
\end{verbatim}%$
\[
\begin{array}{ll}
   & \neg (\exists c_1.\, Person(c_1) \wedge \forall x_2.\, \neg Food(x_2) \vee Eats(c_1, x_2)) \\
   \vee & \neg \exists c_8.\, Food(c_4) \wedge \neg \exists c_8.\, Person(c_8) \wedge Eats(c_8, c_4)
\end{array}
\]

\begin{exercise}
  Design a solution where only the |Impl| case of |elimImpAlg| needs to be
  written.
\end{exercise}

\section{Stage 2 -- Move Negation Inwards}

Now that implications are gone, we are left with entirely
symmetrical constructions, and can always push negations
in or out using duality:
\begin{eqnarray*}
  \neg(\neg \phi) & \Leftrightarrow & \phi \\
  \neg(\phi_1 \wedge \phi_2) & \Leftrightarrow & \neg\phi_1 \vee \neg\phi_2 \\
  \neg(\phi_1 \vee \phi_2) & \Leftrightarrow & \neg\phi_1 \wedge \neg\phi_2 \\
  \neg(\exists x.\, \phi) & \Leftrightarrow & \forall x.\, \neg\phi \\
  \neg(\forall x.\, \phi) & \Leftrightarrow & \exists x.\, \neg\phi
\end{eqnarray*}

Our eventual goal is to move negation all the way inward so it is only
applied to atomic predicates.  To express this structure in our types,
we define a new constructor for negated atomic predicates as well as
the type for the output of Stage 2:

\begin{code}
data NAtom a = NAtom String [Term]

instance Functor NAtom where fmap f (NAtom p ts) = NAtom p ts

natom :: (NAtom :<: f) => String -> [Term] -> Formula f
natom p ts = inject (NAtom p ts)

type Stage2 =  TT :+: FF :+: Atom 
               :+: NAtom 
               :+: Or :+: And 
               :+: Exists :+: Forall
\end{code}

One could imagine implementing duality with a multi-parameter type class that records
exactly the dual of each constructor, as
\begin{code}
class (Functor f, Functor g) => Dual f g where
  dual :: f a -> g a
\end{code}

Unfortunately, this leads to a situation where our
subtyping must use the commutativity of
coproducts, which it is incapable of doing
as written.  For this article,
let us just define an algebra to
dualize a whole formula at a time.

\begin{code}
dualize :: Formula Stage2 -> Formula Stage2
dualize = foldFormula dualAlg

class Functor f => Dualize f where
  dualAlg :: f (Formula Stage2) -> Formula Stage2

instance Dualize TT      where dualAlg TT               = ff
instance Dualize FF      where dualAlg FF               = tt
instance Dualize Atom    where dualAlg (Atom p ts)      = natom p ts
instance Dualize NAtom   where dualAlg (NAtom p ts)     = atom p ts
instance Dualize Or      where dualAlg (Or phi1 phi2)   = phi1 `and`  phi2
instance Dualize And     where dualAlg (And phi1 phi2)  = phi1 `or`   phi2 
instance Dualize Exists  where dualAlg (Exists phi)     = forall phi
instance Dualize Forall  where dualAlg (Forall phi)     = exists phi

instance (Dualize f, Dualize g) => Dualize (f :+: g) where
  dualAlg (Inl phi) = dualAlg phi
  dualAlg (Inr phi) = dualAlg phi
\end{code}

Now perhaps the pattern of these transformations is becoming clear.
It is remarkably painless, involving just a little type class syntax
as overhead, to write these functor algebras.  The definition
of |pushNotInwards| is another straightforward fold, with a helper
type class |PushNot|.  I've separated the instance for |Not| since it
is the only one that does anything.

\begin{code}
class Functor f => PushNot f where
  pushNotAlg :: f (Formula Stage2) -> Formula Stage2

instance PushNot Not    where pushNotAlg (Not phi)        = dualize phi

instance PushNot TT     where pushNotAlg TT               = tt
instance PushNot FF     where pushNotAlg FF               = ff
instance PushNot Atom   where pushNotAlg (Atom p ts)      = atom p ts
instance PushNot Or     where pushNotAlg (Or phi1 phi2)   = phi1 `or`   phi2
instance PushNot And    where pushNotAlg (And phi1 phi2)  = phi1 `and`  phi2
instance PushNot Exists where pushNotAlg (Exists phi)     = exists phi
instance PushNot Forall where pushNotAlg (Forall phi)     = forall phi

instance (PushNot f, PushNot g) => PushNot (f :+: g) where
  pushNotAlg (Inr phi) = pushNotAlg phi
  pushNotAlg (Inl phi) = pushNotAlg phi
\end{code}

All we have to do now is define a fold that calls |pushNotAlg|.

\begin{code}
pushNotInwards :: Formula Stage1 -> Formula Stage2
pushNotInwards = foldFormula pushNotAlg
\end{code}

Our running example now becomes:

\begin{verbatim}
*Main> texprint . pushNotInwards . elimImp $ foodFact
\end{verbatim}%$
\[
\begin{array}{ll}
        & (\forall x_1.\, \neg Person(x_1) \vee \exists c_2.\, Food(c_2) \wedge \neg Eats(x_1, c_2)) \\
   \vee & (\forall x_4.\, \neg Food(x_4) \vee \exists c_8.\, Person(c_8) \wedge Eats(c_8, x_4))
\end{array}
\]

\begin{exercise}
  Instead of the |NAtom| constructor, define the composition
  of two functors |f `O` g| and re-write 
  |Stage2 = TT :+: FF :+: Atom :+: (Not `O` Atom) :+: Or :+: And :+: Exists :+: Forall|
\end{exercise}

\begin{exercise}
  Encode a form of subtyping that can reason using commutativity of
  coproducts, and rewrite the |Dualize| algebra using a two-parameter
  |Dual| type class as described above.
\end{exercise}

\section{Stage 3 -- Standardize variable names}

To ``standardize'' variable names means to choose nonconflicting names
for all the variables in a formula.  Since we are using higher-order
abstract syntax, Haskell is handling name conflicts for now.  We can
immediately jump to stage 4!

\section{Stage 4 -- Skolemization}

It is interesting to arrive at the definition of Skolemization via the
Curry-Howard correspondence.  You may be familiar with the idea that
terms of type |a -> b| are proofs of the proposition ``$a$ implies
$b$'', assuming |a| and |b| are interpreted as propositions as well.
This rests on a notion that a proof of |a -> b| must be some process
that can take a proof of |a| and generate a proof of |b|, a very
computational notion.  Rephrasing the above, a function of type |a ->
b| is a guarantee that \emph{for all} elements of type |a|,
\emph{there exists} a corresponding element of type |b|.  So a
function type expresses an alternation of a universal quantifier with
an existential.  We will use this to replace all the existential
quantifiers with freshly-generated functions.  We can of course, pass
a unit type to a function, or a tuple of many arguments, to have as
many universal quantifiers as we like.

Suppose we have $\forall x.\, \forall y.\, \exists z.\, P(x,y,z)$,
then in general there may be many choices for $z$, given a particular
$x$ and $y$.  By the axiom of choice, we can create a function $f$
that associates each $\langle x,y \rangle$ pair with a corresponding
$z$ arbitrarily, and then rewrite the above formula as $\forall x.\,
P(x, y, f(x,y))$.  Technically, this formula is only
equisatisfiable, but by convention I'm assuming
constants to be existentially quantified.

So we need to traverse the syntax tree gathering free variables and
replacing existentially quantified variables with functions of
a fresh name.  Since we are eliminating a binding construct,
we now need to reason about fresh unique names.

Today's formulas are small, so let us use a na\"ive and wasteful
splittable unique identifier supply.  Our supply is an infinite binary
tree, where moving left prepends a |0| to the bit representation of
the current counter, while moving right prepends a |1|.  Hence, the
left and right subtrees are both infinite, nonoverlapping supplies of
identifiers. 
The code for our unique identifier supplies is in Figure~\ref{fig:unq}.

Launchbury and Peyton-Jones \cite{launchbury95state} have
discussed how to use the |ST| monad to implement a much more
sophisticated and space-efficient version of the same idea.

\begin{figure}
  \centering
\begin{code}
type Unique = Int
data UniqueSupply = UniqueSupply Unique UniqueSupply UniqueSupply

initialUniqueSupply :: UniqueSupply
initialUniqueSupply = genSupply 1
  where genSupply n = UniqueSupply n  (genSupply (2*n)) 
                                      (genSupply (2*n+1))

splitUniqueSupply :: UniqueSupply -> (UniqueSupply, UniqueSupply)
splitUniqueSupply (UniqueSupply _ l r) = (l,r)

getUnique :: UniqueSupply -> (Unique, UniqueSupply)
getUnique (UniqueSupply n l r) = (n,l)

type Supply a = State UniqueSupply a

fresh :: Supply Int
fresh = do  supply <- get
            let (uniq,rest) = getUnique supply
            put rest
            return uniq
                       
freshes :: Supply UniqueSupply
freshes = do  supply <- get
              let (l,r) = splitUniqueSupply supply
              put r
              return l
\end{code}  
  \caption{Unique supplies}
  \label{fig:unq}
\end{figure}

%Note to self: this can be improved by, when one name is used, re-interleaving the unused tree.
% perhaps this avoids the Launchbury/Peyton-Jones trickery?
%
%(Looks like this is the composition/coproduct of the Supply monad with the ([Term] ->) monad,
%so let's try to combine it later.)
%
%Instances not involving binders are all identity functions lifted
%into the |[Term] -> Supply a| monad.

The helper algebra for Skolemization is more complex than before because
a |Formula Stage2| is not directly transformed into |Formula Stage4|
but into a function from its free variables to a new formula.  On
top of that, the final computation takes place
in the |Supply| monad because of the need to generate fresh names for
Skolem functions.  Correspondingly, we choose the return type of the algebra to be
|[Term] -> Supply (Formula Stage4)|.  Thankfully, many instances
are just boilerplate.

\begin{code}
type Stage4 = TT :+: FF :+: Atom :+: NAtom :+: Or :+: And :+: Forall

class Functor f => Skolem f where
  skolemAlg ::  f ([Term] -> Supply (Formula Stage4)) 
                -> [Term] -> Supply (Formula Stage4)

instance Skolem TT where 
  skolemAlg TT               xs = return tt
instance Skolem FF where 
  skolemAlg FF               xs = return ff
instance Skolem Atom where 
  skolemAlg (Atom p ts)      xs = return (atom p ts)
instance Skolem NAtom where 
  skolemAlg (NAtom p ts)     xs = return (natom p ts)
instance Skolem Or where 
  skolemAlg (Or phi1 phi2)   xs = liftM2 or  (phi1 xs) (phi2 xs)
instance Skolem And where 
  skolemAlg (And phi1 phi2)  xs = liftM2 and (phi1 xs) (phi2 xs)

instance (Skolem f, Skolem g) => Skolem (f :+: g) where
  skolemAlg (Inr phi) = skolemAlg phi
  skolemAlg (Inl phi) = skolemAlg phi
\end{code}

In the case for a universal quantifier $\forall x.\, \phi$, any
existentials contained within $\phi$ are parameterized by the variable
$x$, so we add $x$ to the list of free variables and Skolemize
the body $\phi$.  Implementing this in Haskell, 
the algebra instance must be a function from
|Forall (Term -> [Term] -> Supply (Formula Stage4))|
to
|[Term] -> Supply (Forall (Term -> Formula Stage4))|,
which involves some juggling of the unique supply.

\begin{code}
instance Skolem Forall where 
  skolemAlg (Forall phi) xs = 
    do  supply <- freshes
        return (forall $ \x -> evalState (phi x (x:xs)) supply)
\end{code}%$

From the recursive result |phi|, we need to construct a new body for
the |forall| constructor that has a \emph{pure} body: It must not run
in the |Supply| monad.  Yet the body must contain only names that do not
conflict with those used in the rest of this fold.  This is why we
need a moderately complex |UniqueSupply| data structure: To break off
a disjoint-yet-infinite supply for use by |evalState| in the body of a
|forall|, restoring purity to the body by running the |Supply|
computation to completion.

Finally, the key instance for existentials is actually quite simple --
just generate a fresh name and apply the Skolem function to all the
arguments |xs|.  The application |phi (Const name xs)| is how we
express replacement of the existentially bound term with |Const name
xs| with higher-order abstract syntax.

\begin{code}
instance Skolem Exists where 
  skolemAlg (Exists phi) xs = 
    do  uniq <- fresh
        phi (Const ("Skol" ++ show uniq) xs) xs
\end{code}

After folding the Skolemization algebra over a formula, Since we are
assuming the formula is closed, we apply the result of folding
|skolemAlg| to the empty list of free variables.  Then the resulting
|Supply (Formula Stage4)| computation is run to completion starting
with the |initialUniqueSupply|.

\begin{code}
skolemize :: Formula Stage2 -> Formula Stage4
skolemize formula = evalState (foldResult []) initialUniqueSupply
  where  foldResult :: [Term] -> Supply (Formula Stage4)
         foldResult = foldFormula skolemAlg formula
\end{code}

And the output is starting to get interesting:
\begin{verbatim}
*Main> texprint . skolemize . pushNotInwards . elimImp $ foodFact
\end{verbatim}%$

\[
\begin{array}{ll}
        & (\forall x_1.\, \neg Person(x_1) \vee Food(Skol_2(x_1)) \wedge \neg Eats(x_1, Skol_2(x_1))) \\
   \vee & (\forall x_2.\, \neg Food(x_2) \vee Person(Skol_6(x_2)) \wedge Eats(Skol_6(x_2), x_2))
\end{array}
\]

In the first line, $Skol_2$ maps a person to a food they don't eat.
In the second line, $Skol_6$ maps a food to a person who doesn't eat it.


\begin{exercise} In the definition of |skolemAlg|, we use |liftM2| to
  thread the |Supply| monad through the boring cases, but the |(->)
  [Term]| monad is managed manually.  Augment the |(->) [Term]| monad
  to handle the |Forall| and |Exists| cases, and then combine this
  monad with |Supply| using either |StateT| or the monad
  coproduct~\cite{monad-coproduct}.  \end{exercise}

\section{Stage 5 -- Prenex Normal Form}

Now that all the existentials have been eliminated, we can also
eliminate the universally quantified variables.  A formula is in
\emph{prenex normal form} when all the quantifiers have been
pushed to the outside of other connectives.  We have already removed
existential quantifiers, so we are dealing only with universal
quantifiers. As long as variable names don't conflict, we can freely
push them as far out as we like and commute all binding sites.  By
convention, free variables are universally quantifed, so a formula is
valid if and only if the body of its prenex form is valid.  Though
this may sound technical, all we have to do to eliminate universal
quantification is choose fresh names for all the variables and forget
about their binding sites.

%data OpenTerm = Constant String [Term]
%              | Var String
%
%data OpenAtom    a = OpenAtom    OpenTerm
%data OpenNAtom a = OpenNAtom OpenTerm
%
%instance Functor OpenAtom    where { fmap _ (OpenAtom x)    = OpenAtom x    }
%instance Functor OpenNAtom where { fmap _ (OpenNAtom x) = OpenNAtom x }

\begin{code}
type Stage5 = TT :+: FF :+: Atom :+: NAtom :+: Or :+: And

prenex :: Formula Stage4 -> Formula Stage5
prenex formula =  evalState  (foldFormula prenexAlg formula) 
                             initialUniqueSupply

class Functor f => Prenex f where
  prenexAlg :: f (Supply (Formula Stage5)) -> Supply (Formula Stage5)

instance Prenex Forall where 
  prenexAlg (Forall phi) = do  uniq <- fresh
                               phi (Var ("x" ++ show uniq))

instance Prenex TT where 
  prenexAlg TT               = return tt
instance Prenex FF where 
  prenexAlg FF               = return ff
instance Prenex Atom where 
  prenexAlg (Atom p ts)      = return (atom p ts)
instance Prenex NAtom where 
  prenexAlg (NAtom p ts)     = return (natom p ts)
instance Prenex Or where 
  prenexAlg (Or phi1 phi2)   = liftM2 or phi1 phi2
instance Prenex And where 
  prenexAlg (And phi1 phi2)  = liftM2 and phi1 phi2

instance (Prenex f, Prenex g) => Prenex (f :+: g) where
  prenexAlg (Inl phi) = prenexAlg phi
  prenexAlg (Inr phi) = prenexAlg phi
\end{code}

Since prenex is just forgetting the binders, our example is mostly unchanged.

\begin{verbatim}
*Main> texprint . prenex . skolemize . pushNotInwards 
                . elimImp $ foodFact
\end{verbatim}%$

\[
\begin{array}{ll}
        & (\neg Person(x_1) \vee Food(Skol_2(x_1)) \wedge \neg Eats(x_1, Skol_2(x_1))) \\
   \vee & (\neg Food(x_2) \vee Person(Skol_6(x_2)) \wedge Eats(Skol_6(x_2), x_2))
\end{array}
\]

\section{Stage 6 -- Conjunctive Normal Form}

Now all we have left is possibly-negated atomic predicates connected
by $\wedge$ and $\vee$.  This second-to-last stage distributes these
over each other to reach a canonical form with all the conjunctions at
the outer layer, and all the disjunctions in the inner layer.

At this point, we no longer have a recursive type for formulas, so
there's not too much point to re-using the old constructors.

\begin{code}
type Literal  = (Atom :+: NAtom) ()
type Clause   = [Literal]  -- implicit disjunction
type CNF      = [Clause]   -- implicit conjunction

(\/) :: Clause -> Clause -> Clause
(\/) = (++)

(/\) :: CNF -> CNF -> CNF
(/\) = (++)
\end{code}

\begin{code}
cnf :: Formula Stage5 -> CNF
cnf = foldFormula cnfAlg

class Functor f => ToCNF f where
  cnfAlg :: f CNF -> CNF

instance ToCNF TT where
  cnfAlg TT               = []
instance ToCNF FF where
  cnfAlg FF               = [[]]
instance ToCNF Atom where
  cnfAlg (Atom p ts)      = [[inj (Atom p ts)]]
instance ToCNF NAtom where
  cnfAlg (NAtom p ts)     = [[inj (NAtom p ts)]]
instance ToCNF And where 
  cnfAlg (And phi1 phi2)  = phi1 /\ phi2
instance ToCNF Or where 
  cnfAlg (Or phi1 phi2)   = [ a \/ b |  a <- phi1, b <- phi2 ]

instance (ToCNF f, ToCNF g) => ToCNF (f :+: g) where
  cnfAlg (Inl phi) = cnfAlg phi
  cnfAlg (Inr phi) = cnfAlg phi
\end{code}

And we can now watch our formula get really large and ugly, as our running example illustrates:
\begin{verbatim}
*Main> texprint . cnf . prenex . skolemize 
                . pushNotInwards . elimImp $ foodFact
\end{verbatim}%$
\[
\begin{array}{ll}
          & (\neg Person(x1) \vee Food(Skol2(x1))\vee \neg Food(x2)\vee Person(Skol6(x2))) \\
   \wedge & (\neg Person(x1) \vee Food(Skol2(x1))\vee \neg Food(x2)\vee Eats(Skol6(x2), x2)) \\
   \wedge & (\neg Person(x1) \vee \neg Eats(x1, Skol2(x1)) \vee \neg Food(x2)\vee Person(Skol6(x2))) \\
   \wedge & (\neg Person(x1)\vee \neg Eats(x1, Skol2(x1))\vee \neg Food(x2)\vee Eats(Skol6(x2), x2))
\end{array}
\]

\section{Stage 7 -- Implicative Normal Form}

There is one more step we can take to remove all those aethetically
displeasing negations in the |CNF| result above, reaching the
particularly elegant \emph{implicative normal form}.  We just gather
all negated literals and push them to left of an implicit implication
arrow, i.e. utilize this equivalence:

\begin{eqnarray*}
   \left( \neg t_1 \vee \cdots \vee \neg t_m \vee t_{m+1} \vee \cdots \vee t_n \right)
   & \Leftrightarrow &
   \left( [t_1 \wedge \cdots \wedge t_m] \Rightarrow [t_{m+1} \vee \cdots \vee t_n] \right)
\end{eqnarray*}

\begin{code}
data IClause =  IClause      -- implicit implication
                  [Atom ()]  -- implicit conjunction
                  [Atom ()]  -- implicit disjunction

type INF = [IClause]         -- implicit conjuction

inf :: CNF -> INF
inf formula = map toImpl formula
    where toImpl disj = IClause  [ Atom p ts  | Inr (NAtom p ts)    <- disj ]
                                 [ t          | Inl t@(Atom  _ _ )  <- disj ]
\end{code}

This form is especially useful for a resolution procedure because
one always resolves a term on the left of an |IClause| with a term
on the right.


\begin{verbatim}
*Main> texprint . inf . cnf . prenex . skolemize 
                . pushNotInwards . elimImp $ foodFact
\end{verbatim}%$

\[
\begin{array}{ll}
          & ([Person(x1) \wedge Food(x2)] \Rightarrow [Food(Skol2(x1)) \vee Person(Skol6(x2))]) \\
   \wedge & ([Person(x1) \wedge Food(x2)] \Rightarrow [Food(Skol2(x1)) \vee Eats(Skol6(x2), x2)]) \\
   \wedge & ([Person(x1) \wedge Eats(x1, Skol2(x1)) \wedge Food(x2)] \Rightarrow [Person(Skol6(x2))]) \\
   \wedge & ([Person(x1) \wedge Eats(x1, Skol2(x1)) \wedge Food(x2)] \Rightarrow [Eats(Skol6(x2), x2)])
\end{array}
\]

\section{Voil\`a}

Our running example has already been pushed all the way through, so now
we can relax and enjoy writing |normalize|.

\begin{code}
normalize :: Formula Input -> INF
normalize =
  inf . cnf . prenex . skolemize . pushNotInwards . elimImp
\end{code}

\section{Remarks}

Freely manipulating coproducts is a great way to make extensible data
types as well as to express the structure of your data and
computation.  Though there is some syntactic overhead, it quickly
becomes routine and readable.  There does appear to be additional
opportunity for scrapping boilerplate code.  Ideally, we could
elminate both the cases for uninteresting constructors and all the
``glue'' instances for the coproduct of two functors.  Perhaps given
more first-class manipulation of type classes and
instances~\cite{typeclasses} we could express that a coproduct has
only one reasonable implementation for \emph{any} type class that is
an implemention of a functor algebra, and never write an algebra instance
for |(:+:)| again.

Finally, Data Types \`a la Carte is not the only way to implement
coproducts.  In Objective Caml, polymorphic variants~\cite{ocaml-variants}
serve a similar purpose, allowing free recombination of variant tags.  The HList library~\cite{hlist}
also provides an encoding of polymorphic variants in Haskell.

\section{About the Author}

Kenneth Knowles is a graduate student at the University of California, Santa Cruz, studying type systems, concurrency, and parallel programming.
He maintains a blog of mathematical musings in Haskell at \url{http://kennknowles.com/blog}

\bibliography{Kenn}

\appendix

\ignore{
\begin{code}
class Pretty a where
    pretty :: a -> Doc

instance PrettyAlg f => Pretty (Formula f) where
  pretty formula = evalState 
                     (foldFormula prettyAlg formula) 
                     initialUniqueSupply

class Functor f => PrettyAlg f where
  prettyAlg :: f (Supply Doc) -> Supply Doc

instance PrettyAlg Atom  where 
  prettyAlg (Atom p t)  = return . pretty $ Const p t

instance PrettyAlg NAtom where 
  prettyAlg (NAtom p t) = textM "~" <--> (return . pretty $ Const p t)

instance PrettyAlg TT   where prettyAlg _          = textM "TT"
instance PrettyAlg FF   where prettyAlg _          = textM "FF"
instance PrettyAlg Not  where prettyAlg (Not a)    = textM "~" <--> parensM a 
instance PrettyAlg Or   where prettyAlg (Or a b)   = a <++> textM "\\/" <++> b
instance PrettyAlg And  where prettyAlg (And a b)  = a <++> textM "/\\" <++> b
instance PrettyAlg Impl where prettyAlg (Impl a b) = a <++> textM "=>"  <++> b

instance PrettyAlg Forall where 
  prettyAlg (Forall t) = do uniq <- fresh
                            let name = "x" ++ show uniq
                            textM "ALL" <++> textM name <++> parensM (t (Var name))

instance PrettyAlg Exists where 
  prettyAlg (Exists t) = do uniq <- fresh
                            let name = "c" ++ show uniq
                            textM "EX" <++> textM name <++> parensM (t (Var name))

instance (PrettyAlg f, PrettyAlg g) => PrettyAlg (f :+: g) where
  prettyAlg (Inl x) = prettyAlg x
  prettyAlg (Inr x) = prettyAlg x

instance (Functor f, PrettyAlg f) => Pretty (f ()) where
  pretty x = evalState (prettyAlg . fmap (const (textM "")) $ x) initialUniqueSupply

instance Pretty CNF where
  pretty formula = sepBy "/\\" $ fmap (parens . sepBy "\\/" . fmap pretty) $ formula


instance Pretty IClause where
    pretty (IClause p q) = (brackets $ sepBy "/\\" $ fmap pretty $ p)
                           <+> text "=>" <+>
                           (brackets $ sepBy "\\/" $ fmap pretty $ q)

instance Pretty INF where
    pretty formula = vcat $ fmap pretty $ formula


instance Pretty Term where
    pretty (Var x)        = text x
    pretty (Const c [])   = text c
    pretty (Const c args) = text c <> parens (sepBy "," (fmap pretty args))

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . render . pretty
\end{code}%$
}

\section{Appendix -- \LaTeX Printing}

We need to lift all the document operators into the freshness monad.
I wrote all this starting with a pretty printer, so I just
reuse the combinators and spit out TeX (which doesn't need to
actually be pretty in source form).
%{
%if style == poly
%format <++> = "<\!\!\!" ++ "\!\!\!>"
%format <+> = "<\!\!\!" + "\!\!\!>"
%format <--> = "<\!\!\!-"  "\!\!\!>"
%endif
\begin{code}
sepBy str = hsep . punctuate (text str)
(<++>) = liftM2 (<+>)
(<-->) = liftM2 (<>)
textM = return . text
parensM = liftM parens

class Functor f => TeXAlg f where
  texAlg :: f (Supply Doc) -> Supply Doc

instance TeXAlg Atom where 
  texAlg (Atom p ts)   = return . tex $ Const p ts

instance TeXAlg NAtom where 
  texAlg (NAtom p ts)  = textM "\\neg" <++> (return . tex $ Const p ts)

instance TeXAlg TT where 
  texAlg _             = textM "TT"

instance TeXAlg FF where
  texAlg _             = textM "FF"

instance TeXAlg Not where 
  texAlg (Not a)       = textM "\\neg" <--> parensM a

instance TeXAlg Or where 
  texAlg (Or a b)      =  parensM a 
                          <++> textM "\\vee" 
                          <++> parensM b

instance TeXAlg And where 
  texAlg (And a b)     =  parensM a 
                          <++> textM "\\wedge" 
                          <++> parensM b

instance TeXAlg Impl where 
  texAlg (Impl a b)    =  parensM a 
                          <++> textM "\\Rightarrow" 
                          <++> parensM b

instance TeXAlg Forall where 
  texAlg (Forall t)    = do  uniq <- fresh
                             let name = "x_{" ++ show uniq ++ "}"
                             textM "\\forall" 
                               <++> textM name 
                               <--> textM ".\\," 
                               <++> parensM (t (Var name))

instance TeXAlg Exists where 
  texAlg (Exists t)    = do  uniq <- fresh
                             let name = "c_{" ++ show uniq ++ "}"
                             textM "\\exists" 
                                <++> textM name 
                                <--> textM ".\\," 
                                <++> parensM (t (Var name))
\end{code}
\begin{code}
instance (TeXAlg f, TeXAlg g) => TeXAlg (f :+: g) where
  texAlg (Inl x)  = texAlg x
  texAlg (Inr x)  = texAlg x

class TeX a where
    tex :: a -> Doc

instance TeXAlg f => TeX (Formula f) where
  tex formula = evalState 
                  (foldFormula texAlg formula) 
                  initialUniqueSupply

instance (Functor f, TeXAlg f) => TeX (f ()) where
  tex x = evalState 
            (texAlg . fmap (const (textM "")) $ x) 
            initialUniqueSupply

instance TeX CNF where
  tex formula = sepBy "\\wedge" 
                $ fmap (parens . sepBy "\\vee" . fmap tex) formula


instance TeX IClause where
    tex (IClause p q) = (brackets $ sepBy "\\wedge" $ fmap tex $ p)
                        <+> text "\\Rightarrow" 
                        <+> (brackets $ sepBy "\\vee" $ fmap tex $ q)

instance TeX INF where
    tex formula = sepBy "\\wedge" $ fmap (parens . tex) $ formula


instance TeX Term where
    tex (Var x)         = text x
    tex (Const c [])    = text c
    tex (Const c args)  = text c <> parens (sepBy "," (fmap tex args))

texprint :: TeX a => a -> IO ()
texprint = putStrLn . render . tex
\end{code}%$
%}
\end{document}

