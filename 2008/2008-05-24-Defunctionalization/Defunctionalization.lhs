
What is defunctionalization?

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

I recently gave a little demonstration entitled "What is Defunctionalization?"
for UCSC TWIGS (the acronym, stolen from a similar seminar in the the U. Mass.
math department, stands for The "What Is … ?" Graduate Seminar). The
inspiration for this talk was just to present what I'd learned after Conor
McBride's brilliant presentation at POPL'08 drove me to put the words "Olivier
Danvy defunctionalize continuation" into Google.

I coded the simplest examples from

 * Defunctionalization at work. O Danvy, LR Nielsen. PPDP 2001.

in literate Haskell for the audience, and also showed off QuickCheck a little
to make sure the translation was correct (finding one error, if I recall).

This blog post is a merging of my talk outline and new stuff that came up live.
Try loading it up in GHCi or Haskell-mode and running the examples and
QuickCheck properties.

> {-# LANGUAGE RankNTypes #-}

> import Prelude hiding (reverse)
> import Control.Monad
> import Control.Monad.Cont
> import Test.QuickCheck

Broadly, defunctionalization is transforming a program to eliminate higher-order functions. Rather than focus on its use for compilation (see this H Cejtin, S Jagannathan, S Weeks paper on MLTon) or analyses (see Firstify from N Mitchell and C Runciman). I wanted to emphasize its use in understanding your own program, along the lines of Wand's Continuation-Based Program Transformation Strategies (JACM 1980).

Here is the first example from Danvy.

> aux1 :: (Int -> Int) -> Int
> aux1 f = f 1 + f 10
>
> main1 x y b = (aux1 (\z -> x + z)) * 
>               (aux1 (\z -> if b then y + z else y - z))

Defunctionalization replaces all the first-class functions with an explicit data structure Lam1 and a global apply1 function, essentially embedding a mini-interpreter for just those lambda terms occurring in the program.

> data Lam1 = Lam1A Int      -- (Lam1A x)   ~ (\z -> x + z)
>           | Lam1B Int Bool -- (Lam1B y b) ~ (\z -> if b then y + z else y - z)
>
> apply1 :: Lam1 -> Int -> Int
> apply1 (Lam1A x)   z = x + z
> apply1 (Lam1B y b) z = if b then y + z else y - z
>
> aux1defun :: Lam1 -> Int
> aux1defun f = (apply1 f 1) + (apply1 f 10)
>
> main1defun x y b = (aux1defun (Lam1A x)) *
>                    (aux1defun (Lam1B y b))

Is it correct? Ask quickcheck:

> prop1 x y b = (main1 x y b == main1defun x y b)

*Main> quickCheck prop1
+++ OK, passed 100 tests.

Next example: flattening a binary tree

> data BinaryTree a = Leaf a
>                   | Node (BinaryTree a) (BinaryTree a)

First, there is the straightforward, inefficient version of flatten

> flatten (Leaf x) = [x]
> flatten (Node t1 t2) = (flatten t1) ++ (flatten t2)

We can represent our output with difference lists offering O(1) append.

> flatten' t = walk t []
>   where walk (Leaf x)     = (x:)
>         walk (Node t1 t2) = (walk t1) . (walk t2)

And now that we've introduced a bunch of first-class functions, let's see what happens when we defunctionalize them.

> data LamBTree a = LamBTreeA a -- (x:)
>                 | LamBTreeB (LamBTree a) (LamBTree a) -- (u . v)
>
> applyBTree (LamBTreeA x)   l = x:l
> applyBTree (LamBTreeB u v) l = applyBTree u (applyBTree v l)
>
> flatten_defun t = applyBTree (walk t) []
>   where walk (Leaf x)     = LamBTreeA x
>         walk (Node t1 t2) = LamBTreeB (walk t1) (walk t2)

Note how LamBTree looks just like the definition of BinaryTree, because it is a catamorphism, hence a hylomorphism, i.e. a recursive function with a call tree that looks like a BinaryTree or whatever structure you are hylo'ing over. (See Sorting morphisms for a beautiful examples of using this to understand your program (L Augusteijn. AFP 1998)). So walk is pretty much the identity function on trees, and then applyBTree is a flatten function with an accumulating parameter. Ignoring the intermediate structure, then we see defunctionalization as a way to derive accumulating parameters.

> prop_flatten :: BinaryTree Int -> Bool
> prop_flatten t = (flatten_defun t == flatten t)

*Main> quickCheck prop_flatten
OK, passed 100 tests

Defunctionalization as an inverse to church encoding

This was possibly my favorite part of Danvy's paper, but I unfortunately had to elide it from my talk as being slightly too esoteric for the mixed crowd.

Let us suppose that tuples were not built in to Haskell but we needed to make them ourselves. The data type and destructors would look like this:

> data MyPair a b = P a b 
>                 deriving (Eq,Show)
>
> myPair x y    = P x y
> myFst (P x y) = x
> mySnd (P x y) = y

And we can ask Quickcheck to test extensionality.

> prop_pair :: MyPair Int Int -> Bool
> prop_pair p = (p == myPair (myFst p) (mySnd p))

*Main> quickCheck prop_pair
+++ OK, passed 100 tests.

So, if you recall whatever lambda-calculus course you may have taken, we can represent them with only functions. I like having rank-N type available for this.

> type ChurchPair a b = (forall c . a -> b -> (a -> b -> c) -> c)

> churchPair x y = (\operation -> operation x y)
> churchFst  p   = p (\x y -> x)
> churchSnd  p   = p (\x y -> y)

Rather than make an Arbitrary instance, I'll settle for reduction rules in this case.

> prop_churchPair :: Int -> Int -> Bool
> prop_churchPair x y = (x == churchFst (churchPair x y)) &&
>                       (y == churchSnd (churchPair x y))

*Main> quickCheck prop_churchPair
+++ OK, passed 100 tests.

But now I've introduced a bunch of higher-order functions, so we just have to see how they defunctionalize!

> data LamSelector = LamFst | LamSnd
> applySelector (LamFst) x y = x
> applySelector (LamSnd) x y = y
>
> data LamPair a b = LamPair a b
> applyPair (LamPair x y) operation = applySelector operation x y
>
> defunPair x y = (LamPair x y)
> defunFst  p   = applyPair p LamFst
> defunSnd  p   = applyPair p LamSnd

You can see that this just reproduces the original, modulo inlining!

Now let's church-encode BinaryTree as its own fold (or catamorphism, if you like). So we have something to defunctionalize, let's write churchDepth to calculate the depth of the tree.

> type ChurchTree a = forall c. (a -> c) -> (c -> c -> c) -> c

> churchLeaf x     = \onLeaf onNode -> onLeaf x
> churchNode t1 t2 = \onLeaf onNode -> onNode (t1 onLeaf onNode) (t2 onLeaf onNode)
>
> churchFold onLeaf onNode t = t onLeaf onNode

> churchDepth t = t (\x -> 0) (\d1 d2 -> 1 + (d1 `max` d2))

Acknowledging that the church encoding is just the fold, we can defunctionalize the fold over any functor to recover the data type. Anyhow…

> data LamLeaf = LamLeaf -- onLeaf
> applyLeaf LamLeaf x = 0
>
> data LamNode = LamNode -- onNode
> applyNode LamNode d1 d2 = 1 + (d1 `max` d2)
>
> data LamTree a = LamTreeLeaf a   -- churchLeaf
>                | LamTreeNode (LamTree a) (LamTree a) -- churchNode
>
> applyTree (LamTreeLeaf x)     onLeaf onNode = applyLeaf onLeaf x
> applyTree (LamTreeNode t1 t2) onLeaf onNode = 
>   applyNode onNode (applyTree t1 onLeaf onNode)
>                    (applyTree t2 onLeaf onNode)
> depth_defun t = applyTree t LamLeaf LamNode

applyTree is just fold over a tree, as promised, and we've recovered the tree data structure.
Defunctionalize your continuation

Suppose you have a first-order (boring!) program. You can't have any fun until you find a way to introduce some first-class functions. A classic way to introduce a gratuitous number is to convert your code into continuation-passing style. Let's try it.

This is Danvy's ‘s example of a parser to recognize the language 0^n 1^n. It is written with an auxiliary function in the Maybe monad to simulate throwing an exception as soon as we can reject the string.

> recognize :: [Int] -> Bool
> recognize xs = case walk xs of Just [] -> True
>                                _       -> False 
>   where 
>     walk :: [Int] -> Maybe [Int]
>     walk (0:xs') = do remaining <- walk xs'
>                       case remaining of (1:ys) -> Just ys
>                                         _      -> Nothing
>     walk xs = Just xs -- otherwise

The audience insisted that I test this, because it is a bit of a weird way to write a trivial function.

> prop_recognize1 n = recognize (take n (repeat 0) ++ take n (repeat 1))
> prop_recognize2 m n = (m >= 0 && n >= 1 && m /= n) 
>    ==> (not (recognize (take m (repeat 0) ++ take n (repeat 1))))

*Main> quickCheck prop_recognize1
+++ OK, passed 100 tests.
*Main> quickCheck prop_recognize2
+++ OK, passed 100 tests.

Now if we CPS it, we no longer need the Maybe because we can just discard the continuation and return False.

> recognize' :: [Int] -> Bool
> recognize' xs = walk xs (\xs' -> [] == xs')
>   where
>     walk :: [Int] -> ([Int] -> Bool) -> Bool
>     walk (0:xs') k = walk xs' (\rem -> case rem of (1:ys) -> k ys
>                                                    _      -> False)
>     walk xs      k = k xs -- otherwise

And defunctionalizing it

> data Continuation = ContToplevel     -- (\xs' -> null xs')
>                   | ContRecurse Continuation -- (\remaining -> ... )
>
> applyCont ContToplevel    l = (l==[])
> applyCont (ContRecurse k) l = case l of (1:ys) -> applyCont k ys
>                                         _      -> False
>
> recognize'' xs = walk xs ContToplevel
>   where
>     walk (0:xs') k = walk xs' (ContRecurse k)
>     walk xs      k = applyCont k xs

But now we can look and see that the continuation data structure is just implementing natural numbers, so we replace it by an Int.

> applyNumCont 0 []     = True
> applyNumCont k (1:xs) = applyNumCont (k-1) xs
> applyNumCont _ _      = False

> recognize_final xs = walk xs 0
>   where walk (0:xs') k = walk xs' (k+1)
>         walk xs      k = k xs

We get the program we should have written in the first place.

I didn't get to the rest of this in my talk, and anyhow it is most interesting to people who play with operational semantics a lot. This last bit is from Danvy's paper On Evaluation Contexts, Continuations, and The Rest of Computation from the continuation workshop in 2004.

We have a simple arithmetic language, and two ways of giving it a semantics: We can either reduce the expression a single small step, using reduceAllTheWay to normalize it, or we can eval the expression directly to a result.

> data Exp = Value Int
>          | Add Exp Exp
>
> reduce :: Exp -> Exp
> reduce (Add (Value v1) (Value v2)) = Value (v1 + v2)
> reduce (Add (Value v1) e2        ) = Add (Value v1) (reduce e2)
> reduce (Add e1         e2        ) = Add (reduce e1) e2
>
> reduceAllTheWay :: Exp -> Int
> reduceAllTheWay (Value v) = v
> reduceAllTheWay e = reduceAllTheWay (reduce e)
>
> eval :: Exp -> Int
> eval (Value v)   = v
> eval (Add e1 e2) = (eval e1) + (eval e2)

Now we CPS both of them

> reduceCPS :: Exp -> (Exp -> a) -> a
> reduceCPS (Add (Value v1) (Value v2)) k = k (Value (v1 + v2))
> reduceCPS (Add (Value v1) e2        ) k = reduceCPS e2 (\e -> k (Add (Value v1) e))
> reduceCPS (Add e1         e2        ) k = reduceCPS e1 (\e -> k (Add e e2))
>
> reduceAllTheWayCPS :: Exp -> (Int -> a) -> a
> reduceAllTheWayCPS (Value v) k = k v
> reduceAllTheWayCPS e         k = reduceCPS e (flip reduceAllTheWayCPS k)

> evalCPS :: Exp -> (Int -> a) -> a
> evalCPS (Value v)   k = k v
> evalCPS (Add e1 e2) k = evalCPS e1 (\v1 -> evalCPS e2 (\v2 -> k (v1 + v2)))

CPS code is easier to read when I write it like this

> evalCPS' :: Exp -> (Int -> a) -> a
> evalCPS' (Value v)   k = k v
> evalCPS' (Add e1 e2) k = evalCPS e1 (\v1 ->
>                          evalCPS e2 (\v2 ->
>                          k (v1+v2)  ))

and I might as well admit that Haskell already has this in the bag

> evalCPS'' :: Exp -> Cont a Int
> evalCPS'' (Value v)   = return v
> evalCPS'' (Add e1 e2) = do v1 <- evalCPS'' e1
>                            v2 <- evalCPS'' e2
>                            return (v1 + v2)

Now we defunctionalize both semantics

> data ContReduce = ContReduce  -- (flip reduceAllTheWay)
>                 | ContAddV1 Exp ContReduce -- (\e -> Add (Value v1) e)
>                 | ContAddE2 ContReduce Exp -- (\e -> Add e e2)
>
> applyContReduce :: ContReduce -> Exp -> Exp
> applyContReduce ContReduce e = e
> applyContReduce (ContAddV1 v1 k) e = applyContReduce k (Add v1 e)
> applyContReduce (ContAddE2 k e2) e = applyContReduce k (Add e e2)
>
> reduceCPSdefun :: Exp -> ContReduce -> Exp
> reduceCPSdefun (Add (Value v1) (Value v2)) k = applyContReduce k (Value (v1 + v2))
> reduceCPSdefun (Add (Value v1) e2        ) k = reduceCPSdefun e2 (ContAddV1 (Value v1) k)
> reduceCPSdefun (Add e1         e2        ) k = reduceCPSdefun e1 (ContAddE2 k e2)

The data type ContReduce is the now-common notion of an "evaluation context" which some researchers prefer because it separates the important rules about how terms are reduced from the rules that just tell you where in a term reduction happens.

Next…

> data ContEval = ContEval -- toplevel
>               | ContE1 ContEval Exp
>               | ContE2 Int ContEval
>
> applyContEval :: ContEval -> Int -> Int
> applyContEval (ContEval) v = v
> applyContEval (ContE1 k e2) v1 = evalCPSdefun e2 (ContE2 v1 k) 
> applyContEval (ContE2 v1 k) v2 = applyContEval k (v1 + v2)
>
> evalCPSdefun (Value v)   k = applyContEval k v
> evalCPSdefun (Add e1 e2) k = evalCPSdefun e1 (ContE1 k e2)

Hey it looks like almost the same thing! The difference is in how we interpret the data structure. In the previous case, applyContReduce just used it for navigation. In this case, applyContEval calls back into evalCPSdefun to keep the evaluation rolling.

If, like myself, you liked this because you feel there is important and interesting structure underlying operational semantics that is hidden by its many superficial forms, then you'll probably like this additional reading:

    * Modularity and implementation of mathematical operational semantics. M Jaskelioff, N Ghani, G Hutton. MSFP 2008.
    * Fold and unfold for program semantics. G Hutton. ICFP 1998.

And I leave you with my hidden instances of arbitrary…

> instance Arbitrary a => Arbitrary (BinaryTree a) where
>   arbitrary = oneof [liftM Leaf arbitrary, liftM2 Node arbitrary arbitrary]

> instance (Arbitrary a, Arbitrary b) => Arbitrary (MyPair a b) where
>   arbitrary = liftM2 myPair arbitrary arbitrary


