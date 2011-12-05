Calculating the reflect-rotate-translate normal form for an isometry of the plane in Haskell, and verifying it with QuickCheck.

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

Any isometry of the plane has a unique normal form as the composition of a
translation, rotation and reflection. This note computes this normal form and
tests the implementation using the QuickCheck automated testing tool for
Haskell. To generate random test data, I use another characterization of
isometries as products of up to three reflections. This post is a valid
literate Haskell file, so save it to something like `Isometries.lhs` and run
`ghc --make Isometries`. Then check it with `quickCheck +names Isometries.lhs`.

Two aspects of this post are given about equal weight:

1. The mathematical content is elementary and can be understood by anyone
familiar with basic trigonometry, as you might learn in high school. It is
inspired by the book Symmetries by DL Johnson, one of the very excellent
Springer Undergraduate Mathematics Series.

2. The tool [QuickCheck](http://www.math.chalmers.se/~rjmh/QuickCheck/) is a
fairly brilliant and easy-to-use automatic testing library for Haskell. I use
it to verify each step of the post. All but the first of my QuickCheck
properties found real errors!

> module Main where
> import Test.QuickCheck

Now, the reflect-rotate-translate normal form is defined relative to a point P
(the center of rotation) and a line L (of reflection). Concisely: f = t \circ s
\circ r where t is a translation, s is a rotation about P, and r is a
reflection about L (allowing the identity to be considered a reflection).

I will choose P = (0,0) and L = the X axis since they are simple.

> newtype Translation = Translate (Double, Double) deriving Show
> newtype Rotation    = Rotate Double deriving Show
> newtype Reflection  = Reflect Bool deriving Show
>
> translate (Translate (dx,dy)) (x,y) = (x+dx,y+dy)
> rotate (Rotate angle) (x,y) = (x * cos angle - y * sin angle,
>                                x * sin angle + y * cos angle)
> reflect (Reflect b) (x,y) = if b then (x,-y) else (x,y)
>
> type IsometryNF = (Translation, Rotation, Reflection) 
> apply (t, s, r) (x,y) = (translate t . rotate s . reflect r) (x,y)

Aside from preserving distances, the other key aspect of an isometry is that it
is invertible, so let's express the invertibility of these basic isometries
with a Haskell type class.

> class Invertible a where
>   inverse :: a -> a
>
> instance Invertible Translation where
>   inverse (Translate (dx,dy)) = (Translate (-dx,-dy))
>
> instance Invertible Rotation where
>   inverse (Rotate angle) = Rotate (-angle)
>
> instance Invertible Reflection where
>   inverse (Reflect b) = Reflect b

We can now express the `normalForm` function. As input, it takes an arbitrary
"black-box" isometry as a Haskell function (the type doesn't enforce that the
function is actually an isometry, of course). As each component of the normal
form is computed, the inverse of that component is applied before calculating
the next component.

> type Point2D = (Double,Double)
> type Map2D = Point2D -> Point2D
> data Isometry = Isometry Map2D
>
> normalForm :: Isometry -> IsometryNF
> normalForm (Isometry f) = (t, s, r)
>   where t = translation f
>         s = rotation (translate (inverse t) . f)
>         r = reflection (rotate (inverse s) . translate (inverse t) . f)

The rest of this post is writing and specifying the `translation`, `rotation`, and
`reflection` helper functions. As an example, I've created this isometry using
[GeoGebra](http://www.geogebra.org/). I will maintain the convention that the
source objects are blue and the output of a transformation is red. 

isom2.png

Since reflections and rotations fix the origin, the translation is just
wherever the origin gets sent.

> translation :: Map2D -> Translation
> translation f = Translate (f (0,0))

On translations, this should be the identity, and we express that fact with the
first of these QuickCheck properties. The second indicates that for an
arbitrary isometry f = t \circ s \circ r, composing with the translation's
inverse should fix the origin, because s and r leave the origin where it is:
t^{-1} \circ f = t^{-1} \circ t \circ s \circ r = s \circ r Or in pictures:

isomtrans.png

The operator `=~=` is an "approximate" equality operator for floating point
numbers.

> prop_translation :: Translation -> Point2D -> Bool
> prop_translation trans (x,y) = translate trans (x,y) =~=
>                                translate (translation (translate trans)) (x,y)
>
> prop_tInv :: Isometry -> Point2D -> Bool
> prop_tInv (Isometry f) (x,y)  =  (tInv . f) (0,0) =~= (0,0)
>   where tInv = (translate . inverse . translation) f

To find the rotation, we pick any point on the X axis and see where it is sent
after inverting the translation. A simple choice is (1,0) which will be rotated
somewhere else on the unit circle.

> rotation :: Map2D -> Rotation
> rotation f = Rotate angle
>   where (x,y) = f (1,0)
>         yAngle = asin y
>         xAngle = acos x
>         angle  = if yAngle > 0 then xAngle else 2*pi - xAngle

To test this function, we use extensional equality on rotation functions rather
than intensional equality on the angle since rotations do not have a unique
representation (our function returns a canonical representation between 0 and
2\pi). As inverting the translation component of an isometry fixes the origin,
inverting this rotation should fix the point (1,0) and by implication the
entire X axis. In pictures:

isomrot.png

> prop_rotation :: Rotation -> Point2D -> Bool
> prop_rotation rot (x,y) = rotate rot (x,y) =~= 
>                            rotate (rotation (rotate rot)) (x,y)
>

> prop_sInv :: Isometry -> Point2D -> Bool
> prop_sInv (Isometry f) (x,y)  =  (sInv . tInv . f) (1,0) =~= (1,0)
>   where tInv = (translate . inverse . translation) f
>         sInv = (rotate . inverse . rotation) (tInv . f)

We have calculated t and s and now we have in hand: s^{-1} \circ t ^{-1} \circ
f = s^{-1} \circ t ^{-1} \circ t \circ s \circ r = r

Now we just figure out the reflection r by choosing any point not on the X axis
and seeing if it was reflected or not. An obvious choice is (0,1)

> reflection :: Map2D -> Reflection
> reflection f = Reflect (not (f (0,1) =~= (0,1)))

The correctness properties should be familiar by now:

> prop_reflection :: Reflection -> Point2D -> Bool
> prop_reflection refl (x,y)  =  reflect refl (x,y) =~=
>                                reflect (reflection (reflect refl)) (x,y)
>
> prop_rInv :: Isometry -> Point2D -> Bool
> prop_rInv (Isometry f) (x,y)  =  (rInv . sInv . tInv . f) (1,0) =~= (1,0)
>   where tInv = (translate . inverse . translation) f
>         sInv = (rotate . inverse . rotation) (tInv . f)
>         rInv = (reflect . inverse . reflection) (sInv . tInv . f)

isomrefl.png

And we are done! To test, though, we need to tell QuickCheck how to generate
isometries. I could reuse the basic isometries, but code duplication is
desirable for consistency checking, so I'll use another mathematical property
to generate random isometries: they are all the composition of three
reflections, which may each be the identity, of course.

Reflecting about an arbitrary line is pretty easy: translate so the line passes
through the origin, rotate the line onto the horizontal axis, then reflect
(sound familiar?). You can read more at Planet Math if you like, or figure out
the formulae yourself with some high school trigonometry, or just let the
computer compose the functions for you. Because I want to decouple my
specifications and implementation, I worked out the formulae directly.

> instance Arbitrary Isometry where
>   arbitrary = do refl1 <- newRefl
>                  refl2 <- newRefl
>                  refl3 <- newRefl
>                  return (Isometry (refl3 . refl2 . refl1))
>       where newRefl = do angle <- arbitrary
>                          yOffset <- arbitrary
>                          return (reflectAbout yOffset angle)
>
> reflectAbout :: Double -> Double -> Map2D
> reflectAbout yOffset angle =
>   translateY yOffset . reflectRotate angle . translateY (-yOffset)
>     where translateY dy (x,y) = (x,y+dy)
>           reflectRotate angle (x,y) = (x * cos (2*angle) + y * sin (2*angle),
>                                        x * sin (2*angle) - y * cos (2*angle))

And we can use QuickCheck to test our generator. (This caught a typo in
`reflectAbout`)

> prop_Isometry :: Isometry -> Point2D -> Point2D -> Bool
> prop_Isometry (Isometry f) p1 p2 =  distsq p1 p2 =~= distsq (f p1) (f p2)
>   where distsq (x,y) (x',y') = (x-x')**2 + (y-y')**2

Then the statement of correctness for the entire algorithm is:

> prop_NF :: Isometry -> Point2D -> Bool
> prop_NF f'@(Isometry f) (x,y)  =  f (x,y) =~= apply (normalForm f') (x,y)

And `normalForm` should also be the identity on normal forms, to check that I've
written `apply` correctly. A lot of these properties overlap so they fail
together, but it doesn't hurt to have a lot of properties.

> prop_NFNF nf (x,y)  =  apply nf (x,y) =~= 
>                        apply (normalForm $ Isometry $ apply nf) (x,y)

The QuickCheck page has a script to run your tests in hugs, but I had to edit
it somewhat to run it on my machine. In case you don't want to do that, this
file can just be compiled and run. Either way you run the checks, then you
should see something like this:

*Main> prop_translation: OK, passed 100 tests.
*Main> prop_tInv: OK, passed 100 tests.
*Main> prop_rotation: OK, passed 100 tests.
*Main> prop_sInv: OK, passed 100 tests.
*Main> prop_reflection: OK, passed 100 tests.
*Main> prop_rInv: OK, passed 100 tests.
*Main> prop_Isometry: OK, passed 100 tests.
*Main> prop_NF: OK, passed 100 tests.
*Main> prop_NFNF: OK, passed 100 tests.

Below here is just boilerplate -- end of commentary.

> main = do check ("prop_translation", prop_translation)
>           check ("prop_tInv", prop_tInv)
>           check ("prop_rotation", prop_rotation)
>           check ("prop_sInv", prop_sInv)
>           check ("prop_reflection", prop_reflection)
>           check ("prop_rInv", prop_rInv)
>           check ("prop_Isometry", prop_Isometry)
>           check ("prop_NF", prop_NF)
>           check ("prop_NFNF", prop_NFNF)
>           
>   where check (name,prop) = do putStr (name ++ ": ")
>                                quickCheck prop
>
> instance Arbitrary Translation where 
>   arbitrary = do dx <- arbitrary
>                  dy <- arbitrary
>                  return (Translate (dx,dy))
>
> instance Arbitrary Rotation where
>   arbitrary = do angle <- arbitrary
>                  return (Rotate angle)
>
> instance Arbitrary Reflection where
>   arbitrary = do refl <- arbitrary 
>                  return (Reflect refl)
>
> instance ApproxEq Rotation where
>   (Rotate a) =~= (Rotate a')  =  a =~= a'
>
> instance Show Isometry where
>   show = show . normalForm -- cheating!
>
> class ApproxEq a where
>   (=~=) :: a -> a -> Bool
>
> instance (ApproxEq a, ApproxEq b) => ApproxEq (a,b) where
>   (x,y) =~= (x',y')  =  (x =~= x') && (y =~= y') 
>     where epsilon = 0.001
>
> instance ApproxEq Double where
>   x =~= x'  =  (abs (x-x') < epsilon)
>     where epsilon = 0.001

