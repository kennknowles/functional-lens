
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

The [call is
out](http://www.haskell.org/pipermail/haskell-cafe/2008-May/042493.html)
for submissions to the next issue of [The
Monad.Reader](http://www.haskell.org/haskellwiki/The_Monad.Reader)!
To get an idea of the content (and because [D Stewart told us all to
read every past
issue](http://www.haskell.org/pipermail/haskell-cafe/2008-May/042580.html))
I cracked open [Issue
10](http://www.haskell.org/sitewiki/images/0/0a/TMR-Issue10.pdf),
which has a nice tutorial by B Pope on the GHCi debugger.

But having just finished [a post using open
recursion](http://www.kennknowles.com/blog/2008/05/07/ctl-model-checking-in-haskell-a-classic-algorithm-explained-as-memoization/),
it immediately cried out to me that open-recursive functions already
have some debugging hooks for tracing/breakpoints/etc.  Naturally,
some complications arose, and I got to try out some other cool ideas
from the literature.

To combine the `State` in which I store the memoization table
with the `IO` I use for debugging, I use

 * [Composing monads using coproducts](http://www.mcs.le.ac.uk/~ng13/papers/icfp02.ps.gz).  C Lüth, N Ghani.  ICFP 2002.

And then to reduce the plumbing overhead I use

 * [Data Types a la Carte](http://www.cs.nott.ac.uk/~wss/Publications/DataTypesALaCarte.pdf).  W Swierstra.  Accepted to JFP.

This post is, as usual, a literate Haskell file so load it up in GHCi
or Emacs Haskell-mode and see what happens.

> {-# LANGUAGE TypeOperators,ScopedTypeVariables,PatternSignatures,RankNTypes,FlexibleInstances,UndecidableInstances,OverlappingInstances,IncoherentInstances,MultiParamTypeClasses,FlexibleContexts #-}

> import qualified Data.Map as M
> import Control.Monad.State hiding (fix)

Here's the previous example of a monadified, open-recursion
fibonacci, 

> type Gen a = (a -> a)
>
> fix :: Gen a -> a
> fix f = f (fix f)
>
> gmFib :: Monad m => Gen (Int -> m Int)
> gmFib recurse 0     = return 0
> gmFib recurse 1     = return 1
> gmFib recurse n = do a <- recurse (n-1)
>                      b <- recurse (n-2)
>                      return (a + b)

... and the [memoization mixin](http://www.cs.utexas.edu/~wcook/Drafts/2006/MemoMixins.pdf)

> type Memoized a b = State (M.Map a b)
>
> memoize :: (Ord a) => Gen (a -> Memoized a b b)
> memoize self x = do memo <- check x
>                     case memo of
>                               Just y  -> return y
>                               Nothing -> do y <- self x
>                                             store x y
>                                             return y
>
> check :: Ord a => a -> Memoized a b (Maybe b)
> check x = do memotable <- get
>              return (M.lookup x memotable)
>
> store :: Ord a => a -> b -> Memoized a b ()
> store x y = do memotable <- get
>                put (M.insert x y memotable)
>
> runMemo :: Ord a => Memoized a b c -> c
> runMemo m = evalState m M.empty
>
> fibMemo n = runMemo $ fix (gmFib . memoize) n

So let us begin debugging.  The first thing that comes to
mind is viewing the results of each recursive call.

> inspect :: (Show a, Show b) => String -> Gen (a -> IO b)
> inspect name self arg = do result <- self arg
>                            putStrLn $ name ++ " " ++ show arg 
>                                       ++ " = " ++ show result
>                            return result

> fibInspect n = fix (gmFib . inspect "fib") n

*Main> fibInspect 5
fib 1 = 1
fib 0 = 0
fib 1 = 1
fib 2 = 1
fib 3 = 2
fib 0 = 0
fib 1 = 1
fib 2 = 1
fib 1 = 1
fib 0 = 0
fib 1 = 1
fib 2 = 1
fib 3 = 2
fib 4 = 3
5

That was easy!  Now when I also mix in the memoization I should see a
lot of those recursive calls drop away.  But I cannot simply write
`fix (gmFib . inspect "fib" . memoize)` because mixing in `inspect`
fixes the underlying monad to `IO`, while mixing in `memoize` fixes it
to `Memoized Int Int`.  I need to run this computation in a monad that
supports the operations of both `IO` and `State`.  Well, in category
theory terms, the smallest
["thing"](http://www.math.harvard.edu/~mazur/preprints/when_is_one.pdf)
that contains two other "things" is their coproduct, so this is
exactly what the Luth-Ghani paper mentioned above is for!

I'll be inlining and de-generalizing a bunch of the (beautiful) code
from the paper to make it look more like something an "in the
trenches" programmer would write.

> data Plus m1 m2 a = T1 (m1 (Plus m1 m2 a))
>                   | T2 (m2 (Plus m1 m2 a))
>                   | Var a

This data type is not _exactly_ the coproduct, but rather a data type
that can represent it, like using a list to represent a set -- there
are more lists than sets, but if you respect the abstraction you are
OK.  Most of the ways of processing this data structure can be written
in Haskell using only `Functor` instances for the underlying
structure, but to make sure we only use it in the appropriate places
I've just made the stronger requirement that `m1` and `m2` be `Monad`s
everywhere.  But I still want `fmap` so I turn on undecidable
instances and add the following.

> instance Monad m => Functor m where
>     fmap f m = m >>= (return . f)

Now you might ask why I'm not using monad transformers.  Four reasons come to mind:

 1. I wanted to try out the contents of this paper.
 2. The coproduct is defined for two arbitrary monads, without writing a special
    version of either that "holds" another inside.
 3. The coproduct can have the two "layers" interleaved in more arbitrary ways
 4. The coproduct is theoretically simpler and more fundamental.

This is now one of those structures that is so abstract that you
can figure out how to process it just by writing
the only function of the proper type.

> fold :: (Monad f1, Monad f2) => -- fold by cases over Plus
>             (a -> b)     -> -- variables
>             (f1 b -> b)  -> -- bits from f1 
>             (f2 b -> b)  -> -- bits from f2
>             Plus f1 f2 a -> -- the input
>             b -- Yay!

> fold e f1 f2 (Var x) = e x
> fold e f1 f2 (T1 t) = f1 (fmap (fold e f1 f2) t)
> fold e f1 f2 (T2 t) = f2 (fmap (fold e f1 f2) t)

> instance (Monad m1, Monad m2) => Monad (Plus m1 m2) where
>     return x = Var x
>     m >>= f = fold f T1 T2 m
 
The functor instance induced by the monad would look like this

 instance (Monad m1, Monad m2) => Functor (Plus m1 m2) where
     fmap f = fold (Var . f) T1 T2

Here `fmap` traverse the shapes of `m1` and `m2` and applies `f` where
it finds a `Var` constructor.  To get a better picture, try combining
the bodies of `fold` and `fmap`:

 fmap f (Var x) = Var (f x)
 fmap f (T1 t) = T1 (fmap (fmap f) t)
 fmap f (T2 t) = T2 (fmap (fmap f) t)

And then we want to be able to inject things from `m1` and `m2` into
the coproduct.

> inl :: Monad m1 => m1 a -> Plus m1 m2 a
> inl = T1 . fmap Var

> inr :: Monad m2 => m2 a -> Plus m1 m2 a
> inr = T2 . fmap Var

> liftL :: Monad m1 => (a -> m1 b) -> (a -> Plus m1 m2 b)
> liftL f = inl . f 

> liftR :: Monad m2 => (a -> m2 b) -> (a -> Plus m1 m2 b)
> liftR f = inr . f 

At this point I've got the machinery to combine the `IO` and `Memoized` monads
as desired, but my code would be full of `inr`, `inl`, `liftL` and `liftR`.
This is where we bring in the Swierstra pearl (used and discussed
all over place: See [Modularity and implementation of mathematical operational semantics](http://www.cs.nott.ac.uk/~gmh/modular.pdf),
[Phil Wadler's blog](http://wadler.blogspot.com/2008/02/data-types-la-carte.html), [a thread on haskell-cafe](http://www.haskell.org/pipermail/haskell-cafe/2008-February/040098.html), and of course [Lambda the Ultimate](http://lambda-the-ultimate.org/node/2700))

Again, I'm specializing all the types to `Monad` for clarity/laziness
but they were presented for more general functors.

> class (Monad smaller, Monad larger) => Included smaller larger where
>     inject :: smaller a -> larger a

> instance Monad f => Included f f where
>     inject = id

> instance (Monad f, Monad g) => Included f (Plus f g) where
>     inject = inl

> instance (Monad f, Monad g) => Included g (Plus f g) where
>     inject = inr

Also, since for this example I don't use nested coproducts I'm leaving
out this instance, which opens of a can of worms:

 instance (Monad f, Monad g, Monad h, Included f h) => Included f (Plus g h) where
    inject = inr . inject

Definitely see the links above if you are curious about how this plays out.

Back to the debugging story.  Here is how we modify `inspect` and `memoize`.

> inspectM :: (Show a, Show b, Monad m, Included IO m) => String -> Gen (a -> m b)
> inspectM name self arg = do result <- self arg
>                             inject $ putStrLn $ name ++ " " ++ show arg 
>                                                 ++ " = " ++ show result
>                             return result

> memoizeM :: (Ord a, Monad m, Included (Memoized a b) m) => Gen (a -> m b)
> memoizeM self x = do memo <- inject $ check x
>                      case memo of
>                               Just y  -> return y
>                               Nothing -> do y <- self x
>                                             inject $ store x y
>                                             return y

> mFibTraceMemo :: Int -> Plus (Memoized Int Int) IO Int
> mFibTraceMemo = fix (gmFib . memoizeM . inspectM "fib")

But wait, how do I run this thing?  It has `IO` and `Memoized` layers
all mixed up!  Intuitively, I'm sure you believe that if I start with
an empty memo table and start running an `IO` that has some memoized
bits in it, I can thread the memo table throughout.

In classic Haskell style, we can separate the "threading" concern from
the "running" by writing an untangling function of type `Plus m1 m2 a
-> m1 (m2 a)`.  But in fact, we don't even need to do that much
work. Discussed but not hacked up in the Luth-Ghani paper is the idea
of a _distributivity law_, which in hacking terms means a function
that just does one bit of the untangling, specifically a single
"untwist" `forall a. m2 (m1 a) -> (m1 (m2 a))`.  If we can write an
untwist function, then a fold over the monad coproduct does the rest
of the untangling.

Let us make this concrete for `IO` and `State`.

> ioState :: IO (State s c) -> State s (IO c)
> ioState io = State $ \s -> ((do st <- io
>                                 return (evalState st s)), s)

This function essentially corresponds to the `MonadIO` instance of the
`StateT` monad transformer.  More generally, Luth-Ghani show that when
you can write one of these distributivity laws, then using the
coproduct is isomorphic to using monad transformers, so I already
knew this part would work out :-)

Here is how we fold an "untwist" into an "untangle"

> distribL :: (Monad m1, Monad m2) => 
>               (forall b. m2 (m1 b) -> m1 (m2 b)) -> -- A flick of the wrist
>               Plus m1 m2 a ->                       -- A tangled skein
>               m1 (m2 a)                             -- A silken thread
> distribL untwist = fold (return . return) join (fmap join . untwist)

It may be easier to see it written out in pointful style.
 
 distribL untwist (Var x) = return (return x)
 distribL untwist (T1 t)  = join (fmap (distribL untwist) t)
 distribL untwist (T2 t)  = fmap join (untwist (fmap (distribL untwist) t))

Another way to convince yourself that your function is correct is to
think... how many functions even have the necessary type?  Not very
many, since you _need_ the higher-rank type for the parameter for this
guy to even type check!  When dealing with very abstract functions, you
often gain enough via parametericity to make up for the loss in intuitive
clarity.

> runMemoIO :: Plus (Memoized a b) IO b -> IO b
> runMemoIO result = evalState (distribL ioState result) M.empty

> fibTraceMemo = runMemoIO . mFibTraceMemo

Now we can visually confirm that it is not repeating any computation:
*Main> fibTraceMemo 10
fib 1 = 1
fib 0 = 0
fib 2 = 1
fib 3 = 2
fib 4 = 3
fib 5 = 5
fib 6 = 8
fib 7 = 13
fib 8 = 21
fib 9 = 34
55

Note that this is a little sensitive to explicit type signatures again.  When I inlined
the body of `mFibTraceMemo` I needed to ascribe a type to `memoizeM` like so:

 memoizeM' :: Gen (Int -> Plus (Memoized Int Int) IO Int) = memoizeM

Now that the vamp is playing, let's riff on it.  How about catching calls to
negative numbers?

> guardedBail :: forall a b m. (Monad m, Included (Memoized a b) m) => 
>                              (a -> Bool) -> Gen (a -> m b)
> guardedBail pred self arg = if pred arg then error "Forbidden!" else self arg

Or suppose we have memory consumption concerns, and we want to watch the size
of the memo table?

> printSize :: forall a b m. 
>              (Monad m, Included (Memoized a b) m, Included IO m) => 
>              Gen (a -> m b)
> printSize self arg = do result <- self arg
>                         size <- inject $ getSize
>                         inject $ putStrLn $ "Memo table size: " ++ show size
>                         return result
>     where getSize :: Memoized a b Int = do memotable <- get
>                                            return $ M.size memotable
 
When I try to separate `getSize` as an independent function (which clearly it is) I get 
type class error message pain, so I left it in the `where` clause.

> mFibSizeTrace :: Int -> Plus (Memoized Int Int) IO Int
> mFibSizeTrace = fix (gmFib . memoizeM . printSize 
>                      . inspectM "fib" . guardedBail (<0)) 

> fibSizeTrace n = runMemoIO $ mFibSizeTrace n

*Main> fibSizeTrace 10
fib 1 = 1
Memo table size: 0
fib 0 = 0
Memo table size: 1
fib 2 = 1
Memo table size: 2
fib 3 = 2
Memo table size: 3
fib 4 = 3
Memo table size: 4
fib 5 = 5
Memo table size: 5
fib 6 = 8
Memo table size: 6
fib 7 = 13
Memo table size: 7
fib 8 = 21
Memo table size: 8
fib 9 = 34
Memo table size: 9
55
*Main> fibSizeTrace (-1)
*** Exception: Forbidden!

Of course, we are storing all these past results that don't matter
anymore.  I can certainly delete the entry that is three less than the
current argument.

> clearPrev :: forall b m. 
>              (Monad m, Included (Memoized Int b) m) => Gen (Int -> m b)
> clearPrev self arg = do inject $ clear (arg - 3)
>                         self arg
>     where clear :: Int -> Memoized Int b ()
>           clear key = do memotable <- get
>                          put (M.delete key memotable)

> mFibFinal :: Int -> Plus (Memoized Int Int) IO Int
> mFibFinal = fix (gmFib . clearPrev . memoizeM . inspectM "fib" 
>                  . guardedBail (<0) . printSize)

> fibFinal n = runMemoIO $ mFibFinal n

*Main> fibFinal 15
Memo table size: 0
fib 1 = 1
Memo table size: 1
fib 0 = 0
Memo table size: 2
fib 2 = 1
Memo table size: 3
fib 3 = 2
Memo table size: 4
fib 4 = 3
Memo table size: 4
fib 5 = 5
Memo table size: 4
fib 6 = 8
Memo table size: 4
fib 7 = 13
Memo table size: 4
fib 8 = 21
Memo table size: 4
fib 9 = 34
Memo table size: 4
fib 10 = 55
Memo table size: 4
fib 11 = 89
Memo table size: 4
fib 12 = 144
Memo table size: 4
fib 13 = 233
Memo table size: 4
fib 14 = 377
610

I have a vague feeling that a real debugging package could be made
from this approach, but at if not at least today was some fun.

