
A cursor graphics DSEL, a cute list representation, and some drawings of fractals.

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

I'm reading the very fun _Measure, Topology, and Fractal Geometry_ by
GA Edgar, and thought I'd hack up some of the examples in Haskell.  So
this post implements cursor graphics in OpenGL in (I think) DSEL
style, demonstrating the `StateT` and `Writer` monad gadgets from the
standard library and a cool "novel representation of lists" due to R
Hughes. On the fractal side, I'll try to convince you that fractals
are not just cute pictures, but extremely important illustrations that
the real numbers are weird.  As usual, you can save this post to
`Fractals.lhs` and compile it with `ghc --make Fractals`

It seems that a couple of people have gone before me making actually
useful fractal packages (the packages are more specifically for
"Iterated Function Systems" and "L-systems", respectively) or prettier
pictures in their blog posts.

 * [IFS](http://hackage.haskell.org/cgi-bin/hackage-scripts/package/IFS-0.1.1)
   (and [related blog entry](http://www.alpheccar.org/en/posts/show/69))
 * [Nymphaea](http://hackage.haskell.org/cgi-bin/hackage-scripts/package/nymphaea-0.2)
 * [Fractal-hs](http://scsibug.com/2007/04/21/mandelbrot-hs/)

But I didn't let that stop me from doing a little hacking.  This
article is hopefully more entertaining to read that a library API. So
let's get started!  

> import Data.IORef
> import Data.List
> import Graphics.Rendering.OpenGL as GL
> import Graphics.UI.Gtk as Gtk
> import Graphics.UI.Gtk.OpenGL
> import Control.Monad.Writer
> import Control.Monad.State as S

The state of the cursor is a `pos`ition, `dir`ection, and whether the
`ink` is activated (so I can move it about without drawing lines
everywhere).  The neutral state is at the origin, pointed due east,
with the ink on.

> type Point2 = Vertex2 GLfloat
>
> data CursorState = TS { pos :: Point2
>                       , dir :: Float
>                       , ink :: Bool }
>
> neutral = TS { pos = Vertex2 0 0
>              , dir = 0
>              , ink = True }

Now rather than define the syntax of cursor commands and make
functions for creating and consuming it, I want to embed the commands
into Haskell.  This is quite easy, of course.

> type Instruction = CursorState -> CursorState
>
> leftI    angle s = s { dir = dir s + angle }
> rightI   angle s = s { dir = dir s - angle }
> penI     b     s = s { ink = b }
> forwardI dist  s = s { pos = move (pos s) dist (dir s) }
>     where move (Vertex2 x y) dist dir = Vertex2 (x + dist * cos dir) 
>                                                 (y + dist * sin dir)

A first approach to the semantics is that sequence of commands should
have the state threaded through it.  The type of a program would be
`State CursorState ()` (the unit is because there is no return value).
I would then get the final state of `prog` starting from the neutral
state with `execState program neutral`.

But I don't actually care about the final state; I want to evaluate
this program only for its side effects: Whenever I run a `forward`
command, it should leave a line segment if `ink` was enabled.  This
situation is just what the `Writer` monad is for.  When I move from
`s1` to `s2`, I call `tell [(s1,s2)]` in order to "log" this line
segment 

I actually need to carry the state _and_ the log around, so how do I
combine these monads?  Well, there's a huge trail of literature to
follow on that!  If you are interested, [Composing Monads Using
Coproducts](http://www.cs.le.ac.uk/~nghani/papers/icfp02.ps.gz) by C
Lüth, N Ghani has a canonical way, and lots of references.  But for
today, the officially sanctioned approach is to use a monad
transformer; in many practical cases this coincides with the
coproduct.

So a first attempt at the type of a cursor program would be:

`type CursorProgram = StateT CursorState (Writer [(Point2,Point2)]) ()`

What is all this?  Well, `CursorState` is the state I want to pass
around, and `Writer [(Point2, Point2)]` is the _internal_ monad.  The
type is large, but it says a lot!  I have a state that is getting
passed along, and a log that is being kept.  The only thing I have to
watch for is to use `lift . tell` instead of `tell` because I need to
apply it to the inner `Writer`.

But you [shouldn't use list append for a log in real
life](http://www.haskell.org/all_about_monads/html/writermonad.html).
In the above hypothetical definition, the log is a list, so every time
computations are combined with `>>=` the writer monad will invoke a
potentially-costly list append operation.  The log will always grow
from its tail, so I can build the list backwards and it would be
efficient, but there is a cooler trick (actually already available as
the [dlist library](http://hackage.haskell.org/cgi-bin/hackage-scripts/package/dlist),
named for "difference lists"), from this paper:

 * A novel representation of lists and its application to the function
   "reverse".  RJM Hughes.  Information Processing Letters.  1986

In a nutshell: lists and partial applications of `(++)` are in bijection,
so I can swap them.  Here's the definition and bijection.

> newtype List a = L ([a] -> [a])
> instance Monoid (List a) where
>     mappend (L x) (L y) = L (x . y)
>     mempty = L id

> inject :: [a] -> List a
> inject l = L (l++)

> recover :: List a -> [a]
> recover (L list) = list []

> singleton :: a -> List a
> singleton x = L (x:)

Notice how if I append a bunch of singletons, it is the same number
of applications of `:` as if I had built the list backwards.  Then
when I `recover` the list it costs O(n), the same as efficient reversal,
so the two are equally good strategies in this case.  It would be
best to make a `newtype` for backwards lists with its own monoid 
instance anyhow, so the programming overhead is also the same.

Now I just wrap all the instructions to operate on this more-complicated
state, adding logging to `forward`.

> type CursorProgram = StateT CursorState (Writer (List (Point2,Point2))) ()
>
> liftI :: (CursorState -> CursorState) -> CursorProgram
> liftI instr = S.put . instr =<< S.get

> forward, left, right :: Float -> CursorProgram
> left    angle = liftI (leftI angle)
> right   angle = liftI (rightI angle)
> forward dist  = do s <- S.get
>                    liftI (forwardI dist)
>                    s' <- S.get
>                    when (ink s) $ lift $ tell $ singleton (pos s, pos s')

> pen :: Bool -> CursorProgram
> pen b = liftI (penI b)

> run :: CursorProgram -> CursorState -> [(Point2,Point2)]
> run prog state = recover $ execWriter $ execStateT prog state

That's not so bad, is it?  So now let's get on to some drawing.

Possibly the simplest fractal (I'm not actually sure if everyone
agrees about this falling under the definition of "fractal") that
already can blow your mind is the [Cantor Set](http://en.wikipedia.org/wiki/Cantor_set).

> cantor :: Int -> CursorProgram
> cantor depth = cantor' depth 1.0
>   where cantor' 0 size = forward size
>         cantor' n size = do cantor' (n-1) (size/3)
>                             pen False
>                             forward (size/3)
>                             pen True
>                             cantor' (n-1) (size/3)

Viewing that won't be very interesting; it is just an excuse to talk
about it.  But Wikipedia has a nice image:

![cantor_iters.png]

Take the segment $latex [0,1]$ and
remove the center third of it, keeping the endpoints intact.
Now remove the center third of each of those segments, and again,
and again.  Taking the intersection of all of these sets (i.e.
the limit) gives the Cantor Set.

So what does it look like?  Well, it isn't empty, since every point
that is ever an endpoint sticks around forever.  But those aren't the
only points: Convince yourself that $latex \frac 1 4$ is in the set.
I'm pretty sure this can be phrased as a coinductive proof ([link to
metric coinduction]).

The classic way of understanding the Cantor Set is to use ternary
digits.  See if you can convince yourself that the cantor set contains
every real number that doesn't require a 1 in its ternary expansion
(hint: 0.0222222... = 0.1 so 0.1 doesn't _require_ a 1 in its ternary
expansion)

So any number made of a possibly-infinite string of 0s and 2s is in
there.  Sound familiar?  Well, if we use "1" instead of "2" then we
are talking about all possibly-infinite binary strings, which a
programmer should intuitively see is all real numbers in $latex
[0,1]$.  So the Cantor Set is, in fact, uncountable!

Next, how about the [Koch curve](http://en.wikipedia.org/wiki/Koch_curve)?

> koch :: Int -> CursorProgram
> koch depth = koch' depth 1.0
>   where koch' 0 size = forward size
>         koch' n size = do koch' (n-1) (size/3)
>                           left (pi/3)
>                           koch' (n-1) (size/3)
>                           right (pi * 2/3)
>                           koch' (n-1) (size/3)
>                           left (pi/3)
>                           koch' (n-1) (size/3)

![Koch1.small.png]
![Koch2.small.png]
![Koch3.small.png]

This curve (in the limit) is continuous everywhere but differentiable nowhere.

But what is more fun is when you stick three of them end-to-end, for Koch's
Snowflake.

> kochFlake :: Int -> CursorProgram
> kochFlake depth = do -- lining up
>                      pen False
>                      forward 1.0
>                      right (pi/2)
>                      forward (1 / (2*sqrt(3)))
>                      right (pi/2)
>                      pen True
>                      -- draw in a triangle shape
>                      koch depth
>                      right (2*pi/3)
>                      koch depth
>                      right (2*pi/3)
>                      koch depth

Here, the area is obviously finite, and yet the boundary is infinite.

![KochFlake1.small.png]
![KochFlake2.small.png]
![KochFlake3.small.png]

Finally, there's [Heighwey's dragon](http://en.wikipedia.org/wiki/Dragon_curve).

> heighway :: Int -> CursorProgram
> heighway depth = heighway' depth 1.0 1.0
>   where heighway' 0 size parity = forward size
>         heighway' n size parity = do left (parity * pi / 4)
>                                      heighway' (n-1) (size / sqrt 2) 1
>                                      right (parity * pi / 2)
>                                      heighway' (n-1) (size / sqrt 2) (-1)
>                                      left (parity * pi / 4)

![Heighway1.small.png]
![Heighway2.small.png]
![Heighway3.small.png]

This is what you get if you just keep folding a piece of paper in half
in the same direction, then unfold it and set every fold to a right
angle.  Rather than recite facts from Wikipedia, I'll highly recommend
following the link as it is an article of rare quality.  In fact, all
of the articles about these curves were so unexpectedly satisfying
that I ended up not feeling the need to write much.

![dragon_paper.png]

What all of the above fractal curves except the Koch Snowflake have in
common is self-similarity.  The cantor set is essentially identical to
each of its left and right hand sides, i.e.  it is identical to the
union of two scaled-down copies of itself, as the cursor-graphics code
makes obvious.  I said I wouldn't talk about it, so I'll just mention
that if you write this as $latex C = f_1(C) \cup f_2(C)$ then $f_1$
and $f_2$ are the functions in "iterated function systems.  I highly
recommend a googling, or better yet, the book which prompted this
post.

Below is the actual nitty-gritty OpenGL, Gtk, and IO code that plugs it together.

> render :: CursorProgram -> IO ()
> render fractal = do
>   clear [ColorBuffer]
>   loadIdentity
>   color3f (Color3 1 1 1)
>   translate3f $ Vector3 (-0.5) 0 0
>   renderPrimitive Lines $ mapM_ vertex $ combine $ run fractal neutral
>   where color3f = color :: Color3 GLfloat -> IO ()
>         translate3f = translate :: Vector3 GLfloat -> IO ()
>         scale3f = scale :: GLfloat -> GLfloat -> GLfloat -> IO ()
>         combine = concatMap (\(start,end) -> [start,end])

> draw :: GLDrawingArea -> IO () -> IO ()
> draw canvas render = do
>   -- This is all Gtk code, managing the internal structures
>   glContext <- glDrawingAreaGetGLContext canvas
>   glWin <- glDrawingAreaGetGLWindow canvas
>   (w,h) <- glDrawableGetSize glWin
>
>   -- These are OpenGL calls to scale up and use the whole canvas
>   (pos, _) <- GL.get viewport
>
>   -- This is again Gtk code
>   glDrawableGLBegin glWin glContext
>   viewport $= (pos, Size (fromIntegral w) (fromIntegral h))
>   render
>   GL.flush -- except this
>   glDrawableSwapBuffers glWin
>   glDrawableGLEnd glWin

> main = do
>   initGUI
>   glConfig <- glConfigNew [GLModeRGBA, GLModeDouble]
>   initGL
>
>   depthRef <- newIORef 0
>   fractalRef <- newIORef cantor
>
>   canvas  <- glDrawingAreaNew glConfig
>   let redraw = do depth <- readIORef depthRef
>                   fractal <- readIORef fractalRef
>                   draw canvas (render (fractal depth))
>
>   onExpose canvas (\_ -> do { redraw; return True } )
>
>   buttonBox <- vBoxNew False 0
>
>   incrButton <- buttonNew
>   Gtk.set incrButton [ buttonLabel := "More iterations." ]
>   onClicked incrButton (do oldval <- readIORef depthRef
>                            putStrLn $ show (oldval + 1) ++ " iterations!"
>                            writeIORef depthRef (oldval + 1)
>                            redraw)
>
>   decrButton <- buttonNew
>   Gtk.set decrButton [ buttonLabel := "Less iterations." ]
>   onClicked decrButton (do oldval <- readIORef depthRef
>                            putStrLn $ show (max 0 (oldval - 1)) ++ " iterations!"
>                            writeIORef depthRef (max 0 (oldval - 1))
>                            redraw)
>
>   boxPackStart buttonBox incrButton PackNatural 0
>   boxPackStart buttonBox decrButton PackNatural 0
>
>   dummy <- radioButtonNew -- All buttons join this group
>   mapM_ (\(fun,label) -> do button <- radioButtonNewWithLabelFromWidget dummy label
>                             onToggled button (do me <- toggleButtonGetActive button
>                                                  when me $ do writeIORef fractalRef fun
>                                                  redraw)
>                             boxPackStart buttonBox button PackNatural 0)
>             [ (cantor, "Cantor Set")
>             , (koch, "Koch Curve")
>             , (kochFlake, "Koch Flake")
>             , (heighway, "Heighway Dragon") ]
>
>   canvasBox <- hBoxNew False 0
>   boxPackStart canvasBox buttonBox PackNatural 0
>   boxPackStart canvasBox canvas PackGrow 0
>
>   window <- windowNew
>   Gtk.set window [ containerBorderWidth := 10,
>                    containerChild := canvasBox ]
>   onDestroy window mainQuit
>
>   widgetShowAll window
>   mainGUI
