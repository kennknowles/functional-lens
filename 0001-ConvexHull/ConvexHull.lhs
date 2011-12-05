Visualizing 2D convex hull using Gtk and OpenGL in Haskell
----------------------------------------------------------

<!--
This article original published at http://kennknowles.com/blog

Copyright 2007 Kenneth Knowles

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

This note shows how to use OpenGL with Gtk in Haskell. The result is a little
visualization to check our implementation of the classic iterative convex hull
algorithm. This post is a valid literate Haskell file so save it to something
like `ConvexHull.lhs` and compile with `ghc --make ConvexHull`.  This is what
you'll get when you run `./ConvexHull`:

![Screenshot](hull1.png)

The best OpenGL tutorial for Haskell that I've found is 
[this one from Michi's blog](http://blog.mikael.johanssons.org/archive/2006/09/opengl-programming-in-haskell-a-tutorial-part-1/), 
using GLUT to interface with X. For this tutorial we are going to use the Gtk
`GLDrawingArea` widget, to illustrate the differences, which can be rather hard
to find in the documentation.

The libraries used can be found here:

 * [Haskell OpenGL](http://www.haskell.org/haskellwiki/Opengl)
 * [Gtk2hs](http://haskell.org/gtk2hs/)

These are thin bindings, so our code is all going to be pretty imperative. In the end, this is what we get out:

> import Data.IORef
> import Data.List
> import Graphics.Rendering.OpenGL as GL
> import Graphics.UI.Gtk as Gtk
> import Graphics.UI.Gtk.OpenGL
> import System.Random

I'll show main first. If you are just looking for the outline of how to
initialize everything and make it go, here it is:

> main = do
>   initGUI
>   glConfig <- glConfigNew [GLModeRGBA, GLModeDouble]
>   initGL
>
>   pointRef <- (randomPoints 15 >>= newIORef)
>
>   canvas  <- glDrawingAreaNew glConfig
>   onExpose canvas (\_ -> readIORef pointRef >>= drawWithHull canvas)
>
>
>   button <- buttonNew
>   Gtk.set button [ buttonLabel := "Generate new points." ]
>   onClicked button (do newPoints <- randomPoints 15
>                        writeIORef pointRef newPoints
>                        drawWithHull canvas newPoints
>                        return ())
>
>   vbox <- vBoxNew False 0
>   boxPackStart vbox button PackNatural 0
>   boxPackStart vbox canvas PackGrow 0
>
>   window <- windowNew
>   Gtk.set window [ containerBorderWidth := 10,
>                    containerChild := vbox ]
>   onDestroy window mainQuit
>
>   widgetShowAll window
>   mainGUI

Now, Haskell's OpenGL binding has some quirks with regards to numeric
overloading, so it helps to define some type aliases. Since I want to take
cross products I'll work in three dimensions, and define some basic operations
on my points. The OpenGL binding has separate types for points and vectors, but
I'm going to abuse the point type to represent both.

> type Point3 = Vertex3 GLfloat

> cross :: Point3 -> Point3 -> Point3
> cross (Vertex3 x0 y0 z0) (Vertex3 x1 y1 z1) =
>    Vertex3 (y0*z1 - z0*y1) (z1*x0 - x0*z1) (x0*y1 - x1*y0)

> dot :: Point3 -> Point3 -> GLfloat
> dot (Vertex3 x0 y0 z0) (Vertex3 x1 y1 z1) = x0*x1 + y0*y1 + z0*z1

> randomPoints :: Int -> IO [Point3]
> randomPoints 0 = return []
> randomPoints n = do
>   x <- randomRIO (-0.9,0.9) -- chosen to fit in the OpenGL window
>   y <- randomRIO (-0.9,0.9)
>   rest <- randomPoints (n - 1)
>   return $ Vertex3 x y 0 : rest

Now for the quirks with using Gtk for OpenGL - there are many more setup calls
to make. First, you need to explicitly grab a graphics context `glContext` and
GL drawing window `glWin`. Then, we manage the viewport manually to scale our
rendering up to fill the window. Finally, there are Gtk calls to start and end
OpenGL rendering calls.  It took me a while to discover them.

> drawWithHull :: GLDrawingArea -> [Point3] -> IO Bool
> drawWithHull canvas points = do
>
>   -- This is all Gtk code, managing the internal structures
>   glContext <- glDrawingAreaGetGLContext canvas
>   glWin <- glDrawingAreaGetGLWindow canvas
>   (w,h) <- glDrawableGetSize glWin
>
>   -- This is again Gtk code
>   glDrawableGLBegin glWin glContext
>
>   -- These are OpenGL calls to scale up and use the whole canvas
>   (pos, _) <- GL.get viewport
>   viewport $= (pos, Size (fromIntegral w) (fromIntegral h))
>
>   renderWithHull points
>   GL.flush -- except this
>   glDrawableSwapBuffers glWin
>   glDrawableGLEnd glWin
>   return True

I use the terminology "draw" to refer to Gtk drawing code, which tends to be
bookkeeping, while I use "render" to refer to sequences of OpenGL calls. Here
is the code to actually render the points and their convex hull. Note the
color3f specialization, to help the type inferencer.

> renderWithHull :: [Point3] -> IO ()
> renderWithHull points = do
>   clear [ColorBuffer]
>   color3f (Color3 1 1 1)
>   renderPrimitive Quads $ mapM_ fatPoint $ points
>   color3f (Color3 1 0 0)
>   renderPrimitive LineStrip $ mapM_ vertex $ hull
>     where hull = convexHull points
>           color3f = color :: Color3 GLfloat -> IO ()

> fatPoint (Vertex3 x y z) = do
>   vertex $ Vertex3 (x+0.005) (y+0.005) z
>   vertex $ Vertex3 (x-0.005) (y+0.005) z
>   vertex $ Vertex3 (x-0.005) (y-0.005) z
>   vertex $ Vertex3 (x+0.005) (y-0.005) z

From here on, I'm just implementing the convex hull algorithm.

This is an iterative algorithm that computes the upper half-hull by travelling
left-to-right across the plane making sure to always make right turns; if ever
a left turn occurs, it backtracks as far as necessary, patching up the hull. I
defer the obvious helper `isLeftOf` to the end of the file.

> upperHalfHull points = upperHalfHull' (sort points) []
>    where upperHalfHull' [] hull = hull
>          upperHalfHull' (v:vs) [] = upperHalfHull' vs [v]
>          upperHalfHull' (v:vs) [y] = upperHalfHull' vs [v,y]
>          upperHalfHull' (v:vs) (y:x:zs) = if v `isLeftOf` (x,y)
>                                           then upperHalfHull' (v:vs) (x:zs)
>                                           else upperHalfHull' vs (v:y:x:zs)

Then the lower half of the hull does the same thing right-to-left, and I rather
naively combine them into convexHull (I traverse the points maybe three times
unneccessarily)

> lowerHalfHull points = map rotate180 $ upperHalfHull $ map rotate180 $ points
> rotate180 (Vertex3 x y z) = Vertex3 (-x) (-y) z

> convexHull :: [Point3] -> [Point3]
> convexHull points = upperHalfHull points ++ lowerHalfHull points

There is a divide-and-conquer algorithm which is probably more idiomatic, and
has the same asymptotic complexity (different pathological cases) but this is
the one I was trying out.

This last helper function only makes sense when points are all on the z=0
plane. It takes a point and a directed line segment, and indicates whether the
point lies to the left of the line defined by that segment.

> isLeftOf :: Point3 -> (Point3, Point3) -> Bool
> isLeftOf (Vertex3 x2 y2 _) (Vertex3 x0 y0 _, Vertex3 x1 y1 _) =
>   let Vertex3 _ _ z = (Vertex3 (x1-x0) (y1-y0) 0)
>                       `cross`
>                       (Vertex3 (x2-x0) (y2-y0) 0)
>   in z > 0
