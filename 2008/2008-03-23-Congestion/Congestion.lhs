Using OpenGL's blending to visualize congestion in convex routing (in Haskell)

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

This is a question posed in my randomized algorithms class.  If you
are routing in a network whose connectivity looks "more or less" like
a convex figure, what does the congestion look like?  A quick way to
make an educated guess is to draw a bunch of random line segments in
such a convex shape and see where the colors get the brightest:

![Congestion](Congestion.png)

This post is literate Haskell that will output that image, so save it
to something like `Congestion.lhs` and run `ghc --make
Congestion.lhs`.  I started with the code from [an old
post](http://www.kennknowles.com/blog/2007/11/20/visualizing-2d-convex-hull-using-gtk-and-opengl-in-haskell/)
and cut out the bits I didn't need.  The libraries used can be found
here:

 * [Haskell OpenGL](http://www.haskell.org/haskellwiki/Opengl)
 * [Gtk2hs](http://haskell.org/gtk2hs/)

First, there is the usual administrivia.

> import Data.IORef
> import Data.List
> import Graphics.Rendering.OpenGL as GL hiding (map2)
> import Graphics.UI.Gtk as Gtk hiding (drawSegments, Color)
> import Graphics.UI.Gtk.OpenGL
> import System.Random

Any proper Haskell programmer will of course want to create an
infinite list of random segments,

> type Point3 = Vertex3 GLfloat
>
> randomPoints :: IO [Point3]
> randomPoints = do
>   xgen <- newStdGen
>   ygen <- newStdGen
>   let xs = randomRs (-0.9,0.9) xgen
>   let ys = randomRs (-0.9,0.9) ygen
>   return $ map2 (\x y -> Vertex3 x y 0) xs ys
>     where  map2 f first second = map (uncurry f) (zip first second)

Then `renderSegments` is straightforward.  I draw them very faint gray
so that only in locations of congestion do we see brighter white.

> renderSegments :: [(Point3,Point3)] -> IO ()
> renderSegments segments = do
>   clear [ColorBuffer]
>   color3f (Color3 0.05 0.05 0.05)
>   mapM_ renderSegment segments
>     where
>     color3f = color :: Color3 GLfloat -> IO ()
>     renderSegment (start, end) = renderPrimitive LineStrip $ do vertex start
>                                                                 vertex end

There are a bunch of Gtk and OpenGL calls to add, yielding
`drawSegments` below.  The only thing to note is the setting of
`blendFunc` and `blendAdd` which tell OpenGL to add the color that is
already on a pixel to the color I'm trying to draw.  It is really a
cheap trick to get OpenGL to intersect my line segments and add up the
totals for me.  One gotcha that held me up is that these settings have
to be within the `glDrawableGLBegin` and `glDrawableGLEnd` calls.

> drawSegments :: GLDrawingArea -> [(Point3,Point3)] -> IO Bool
> drawSegments canvas segments = do
>
>   -- This is all Gtk code, managing the internal structures
>   glContext <- glDrawingAreaGetGLContext canvas
>   glWin <- glDrawingAreaGetGLWindow canvas
>   (w,h) <- glDrawableGetSize glWin
>
>   glDrawableGLBegin glWin glContext
>   (pos, _) <- GL.get viewport
>   viewport $= (pos, Size (fromIntegral w) (fromIntegral h))
>   blend $= Enabled
>   blendFunc $= (One, One)
>   blendEquation $= FuncAdd
>   renderSegments segments
>   GL.flush -- except this
>   glDrawableSwapBuffers glWin
>   glDrawableGLEnd glWin
>   return True

And finally we just plug it all together with even more initialization code.

> main = do
>   initGUI
>   glConfig <- glConfigNew [GLModeRGBA, GLModeDouble]
>   initGL
>   startPoints <- randomPoints
>   endPoints <- randomPoints
>   let segments = take 10000 $ zip startPoints endPoints
>
>   canvas  <- glDrawingAreaNew glConfig
>   onExpose canvas (\_ -> drawSegments canvas segments)
>
>   window <- windowNew
>   Gtk.set window [ containerBorderWidth := 10,
>                    containerChild := canvas ]
>   onDestroy window mainQuit
>
>   widgetShowAll window
>   mainGUI
