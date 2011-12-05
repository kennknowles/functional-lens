<!--
This article original published at http://kennknowles.com/blog

Copyright 2008 Kenneth Knowles

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
 
    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

As an exercise, since my reading group was discussing model
checking this week, I implemented the classic model checker
for CTL specifications from the 1986 paper

 * [Automatic Verification of Concurrent Systems Using Temporal Logic Specifications]() by EM Clarke, EM Emerson, AP Sistla.

The "efficient algorithm" presented in the paper is, upon
reflection, merely a memoized traversal of the state machine,
so I combined it with a modified version of

 * [Monadic Memoization Mixins](www.cs.utexas.edu/~wcook/Drafts/2006/MemoMixins.pdf) by D Brown, WR Cook

which actually eliminated an auxilliary function from the algorithm,
and made the Haskell specification of the meaning of CTL connectives
clearer than my English prose!  (But I'll still explain it in English)

> {-# LANGUAGE TypeOperators,ScopedTypeVariables,PatternSignatures #-}

> import qualified Data.Map as M
> import qualified Data.Set as S
> import Data.List
> import Control.Monad 
> import Control.Monad.State hiding (fix)

Here is the easy example from the memoization paper, before getting on to model checking.

To enable functional mixins, we write our functions using
open recursion.  Instead of a function of type `a -> b` 
we write one of type `Gen (a -> b)` and then later
"tie the knot" with `fix` (reproduced here for reference)

> type Gen a = (a -> a)

> fix :: Gen a -> a
> fix f = f (fix f)

The classic example they start with is fibonacci, but don't stop
reading!  It is just to illustrate the technique.

> fib :: Int -> Int
> fib 0     = 0
> fib 1     = 1
> fib (n+2) = fib n + fib (n+1)

By the time you get to `fib 30` it takes a dozen or seconds to return
on my poor old computer.  Rewrittin in open recursion as

> gFib :: Gen (Int -> Int)
> gFib recurse 0     = 0
> gFib recurse 1     = 1
> gFib recurse (n+2) = recurse n + recurse (n+1)

> fib' = fix gFib

This has essentially the same performance, up to constant
factors: slow.

To enable us to store the memoization table in something
like a State monad, parameterize over an underlying
monad.  A beautiful technique in its own right, if you ask
me.

> gmFib :: Monad m => Gen (Int -> m Int)
> gmFib recurse 0     = return 0
> gmFib recurse 1     = return 1
> gmFib recurse (n+2) = do a <- recurse n
>                          b <- recurse (n+1)
>                          return (a + b)

And now we can mix in `memoize`

> type Memoized a b = State (M.Map a b)

> memoize :: Ord a => Gen (a -> Memoized a b b)
> memoize self x = do memo <- check x
>                     case memo of
>                       Just y  -> return y
>                       Nothing -> do y <- self x
>                                     store x y
>                                     return y

> check :: Ord a => a -> Memoized a b (Maybe b)
> check x = do memotable <- get
>              return (M.lookup x memotable)

> store :: Ord a => a -> b -> Memoized a b ()
> store x y = do memotable <- get
>                put (M.insert x y memotable)

Here's the final fib, which returns instantly up to at least `10000`.

> fib'' n = evalState (fix (gmFib . memoize) n) M.empty


CTL

The language for which Clarke et al give a graph-based
algorithm is called CTL (Computation Tree Logic).  It is
a logic for specifying certain restricted kinds of predicates
over the states of a state machine, for today a finite state
machine.

The language of CTL formulas in Haskell looks like this:

> data CTL p = TT | FF
>            | Atomic p
>            | Not (CTL p)
>            | And (CTL p) (CTL p)
>            | AllSucc  (CTL p)
>            | ExSucc   (CTL p)
>            | AllUntil (CTL p) (CTL p)
>            | ExUntil  (CTL p) (CTL p)
>              deriving (Eq,Ord)

Some of the formulae are simply your usual logic

 * `TT` holds of any state
 * `FF` never holds
 * `Atomic p` is some atomic proposition over a state, like inequality over program variables, etc.
 * `Not` and `And` have their expected meanings

The `Succ` construction let you talk about "the next" state.

 * `AllSucc f` (respectively `ExSucc`) holds of a state `s` when the formula `f` holds for all (respectively some) successor states.

The interesting ones though, are "Always Until" and "Exists Until".

 * `AllUntil f1 f2` holds of a state `s` when for _all_ prefixes of any trace starting at `s` you eventually reach a state satisfying `f2`, and everywhere along the way `f1` holds.
 * `ExUntil` is the existential version of that.

We can then define some more predicates like "forever in the future" and "eventually"

> allFuture f = AllUntil TT f
> existsFuture f = ExUntil TT f

> allGlobal f = Not(existsFuture(Not f))
> existsGlobal f = Not(allFuture(Not f))

Now, to apply a formula to a state machine, first I need the state machine.
I'll just represent it by its successor function.

> type Succ st = st -> [st]

And we need some interpretation of atomic formulas as predicates over states

> type Interp p st = p -> st -> Bool

And since I'm using a monadified form of computation, I will lift a bunch
of operations into monads to make everything readable.

> andThen,orElse :: Monad m => m Bool -> m Bool -> m Bool
> andThen = liftM2 (&&) 
> orElse  =  liftM2 (||) 

> notM :: Monad m => m Bool -> m Bool
> notM = liftM not

> anyM,allM :: Monad m => (s -> m Bool) -> [s] -> m Bool
> allM f = liftM and . mapM f
> anyM f = liftM or  . mapM f

THE ALGORITHM

In the Clarke et al paper, the algorithm is expressed by induction
on the formula `f` you want to check:  First, label your state-space
graph with all the atomic formula that hold at each state.  Then,
label with each the compound formula of height two that holds.  Etc, etc,
you are guarantee that the graph is already labelled with subformulas
at each step.  

Like dynamic programming, this is simply a complicated way of expressing
memoization.  In fact, they even use a depth-first search helper
function that is completely eliminated by expressing it as a memoized
function.  This code is considerably shorter and, I think, clearer than
the pseudocode in the paper.

Today we have fancy algorithms involving BDDs and abstraction, so I'm not claiming anything _useful_
except pedagogically.  I do wonder, though, if this code gains something through
laziness.  It certainly traverses the state space fewer times (but I'm sure an implementation
of their algorithm would do similar optimizations).

> checkCTL :: forall p st . (Ord p, Ord st) => 
>                           Interp p st -> Succ st -> st -> CTL p -> Bool
> checkCTL interp succ init f = 
>    evalState (fix (gCheckCTL . cyclicMemoize2 False) f init) M.empty
>  where 
>    gCheckCTL :: Monad m => Gen (CTL p -> st -> m Bool)
>    gCheckCTL recurse f s = checkFormula f
>      where checkFormula TT           = return True
>            checkFormula FF           = return False
>            checkFormula (Atomic p)   = return (interp p s)
>            checkFormula (Not f1)     = notM (recurse f1 s)
>            checkFormula (And f1 f2)  = recurse f1 s `andThen` recurse f2 s
>            checkFormula (AllSucc f1) = allM (recurse f1) (succ s)
>            checkFormula (ExSucc f1)  = anyM (recurse f1) (succ s)

>            checkFormula (AllUntil f1 f2) = recurse f2 s `orElse` 
>                            (recurse f1 s `andThen` allM (recurse f) (succ s))

>            checkFormula (ExUntil f1 f2)  = recurse f2 s `orElse` 
>                            (recurse f1 s `andThen` anyM (recurse f) (succ s))

You notice that I cheated a little, perhaps.  I have used `cyclicMemoize2` instead of `memoize`:

> cyclicMemoize2 :: (Ord a, Ord b) => c -> Gen (a -> b -> Memoized (a,b) c c)
> cyclicMemoize2 backEdge self x y = do memo <- check (x,y)
>                                       case memo of
>                                          Just z  -> return z
>                                          Nothing -> do store (x,y) backEdge
>                                                        z <- self x y
>                                                        store (x,y) z
>                                                        return z

One reason is simply that I need a curry/uncurry wrapper for my two argument monadified function.
The deeper thing is that `cyclicMemoize2 False` inserts a fake memoization entry while a computation
is progressing.  If there is ever a "back edge" in the search, it will return this dummy entry.
For CTL, the auxilliary depth-first search used in the paper for `AllUntil` returns `False` in these 
cases, so I seed the memo table accordingly.  This is because by the time you have recursed
around a cycle, that means that the `f2` you are searching for did not occur on the cycle, so it
never will.

To play with it, I've only made a couple of examples involving stop lights (of occasionally curious colors).  I'd love more, and you'll undoubtedly find
bugs if you actually run something significant.

> ex1interp p s = (p == s)

> ex1succ "Red"    = ["Green"]
> ex1succ "Green"  = ["Yellow"]
> ex1succ "Yellow" = ["Red"]

> ex2succ "Red"    = ["Green"]
> ex2succ "Green"  = ["Yellow", "Orange"]
> ex2succ "Orange" = ["Red"]
> ex2succ "Yellow" = ["Red"]

But it looks kind of OK,

*Main> let ch2 = checkCTL ex1interp ex2succ
*Main> let ch1 = checkCTL ex1interp ex1succ
*Main> ch1 "Red" (existsFuture (Atomic "Red"))
True
*Main> ch1 "Red" (existsFuture (Atomic "Blue"))
False
*Main> ch2 "Green" (ExUntil TT (Atomic "Red"))
True
*Main> ch2 "Green" (ExUntil (Atomic "Green") (Atomic "Orange"))
True
*Main> ch1 "Green" (Not (AllUntil (Not (Atomic "Yellow")) (Atomic "Red")))
True
*Main> ch1 "Green" (Not (ExUntil (Not (Atomic "Yellow")) (Atomic "Red")))
True
*Main> ch2 "Green" (Not (ExUntil (Not (Atomic "Yellow")) (Atomic "Red")))
False

Quite fun!
