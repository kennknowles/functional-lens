
Using HaXml to make a PDF slideshow from an Inkscape SVG

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

I recently got a tablet to input handwritten math for slideshow
presentations, but instead of using a note-taking program (Jarnal,
Xournal, Gournal) I decided that the full power of image manipulation
of a program link Gimp or Inkscape is valuable.  Neither of these,
though, has the same nice support for multi-page documents.  But
Inkscape uses SVG as its native file format, so I wrote this Haskell
script to transform the layers of an Inkscape SVG file into PDF of
slides.  I use the HaXml library to manipulate the SVG, the Inkscape 
command-line interface to convert each page to PDF, and pdftk
to glue the whole thing back together.

For the record, multi-page documents have been on the Inkscape feature
request tracker for many versions, so I presume it is a significant
change.  I _do_ grok C and C++, thanks to the legacy-oriented
education system, but take little enough pleasure from them that I
would rather hack around the issue in Haskell.

> import Text.XML.HaXml
> import Text.XML.HaXml.Pretty
> import Text.XML.HaXml.Posn
> import Text.PrettyPrint.HughesPJ
> import Text.Printf
> import Data.List
> import System.IO
> import System.Cmd

HaXml is based on a combinator library for `CFilter`s to filter, search, output, etc.
It is a little crufty in some ways -- many datatypes are transpararent, and you have
to do a lot of your own set up and tear down.  The expected way to use it seems
to be via `processXmlWith :: CFilter -> IO ()` which is not sufficient for today's
task.  The Hackage documentation pointed to an old version of the API, so I
used the current version of the source code for documentation.  I'd love any
criticism like "you didn't have to do X" or "here is an easier, safer way to do Y".

I couldn't think of a good way to narrate this code, so I'll start
with `main` for a high-level read, and then later fill in all the
helper functions. Naturally we start with a call to `xmlParse`;
the `"-"` is a required filename for error reporting.

> main = do input <- getContents
>           let xml = xmlParse "-" input

Then I grab the names of all the layer objects in the order they
appear in the file, except for the special layer "Background" which
I'll include behind every slide.  The call to `verbatim` spits them
out as `String`s instead of XML `Content`, and the `"-"` is yet
another required filename for error reporting.

>           let names = delete "Background" 
>                       $ map verbatim 
>                       $ filterElem "-" getLayerNames
>                       $ xmlElem 
>                       $ xml
>           putStrLn $ "Making slides from layers:" ++ concatMap ("\n\t"++) names ++ "\n"

Then for each layer, make a new version of the file with just that
layer visible.

>           let outXmls = map (flip selectLayer xml) names
>               usedSlides = take (length names) slideNames
>           mapM_ (uncurry writeFile) (zip (map (++".svg") slideNames) 
>                                          (map (renderStyle xmlStyle . document) outXmls))

And some shell scripting done in Haskell.  I didn't even try to find a scripting
library or anything to protect me from myself building a nasty command line.

>           mapM_ (\slide -> do system $ "inkscape --export-text-to-path --export-pdf='" 
>                                          ++ slide ++ ".pdf' '" ++ slide ++ ".svg'")
>                 usedSlides
>           
>           system $ "pdftk " ++ concat (intersperse " " (map (++".pdf") usedSlides)) 
>                             ++ " cat output Slides.pdf"

So now to the details.

Grabbing the layer names
------------------------

Here is the first helper I wrote, wrapping the `attrval` for a common
case.  This filter returns every tag whose `attr` attribute has the
string value `val`.

> matchAttrString :: String -> String -> CFilter i
> matchAttrString attr val = attrval (attr, AttValue [Left val])

The next helper is one that maps a tag to its attribute value,
otherwise discards anything else it sees.  The HaXml function `iffind`
will pass the `attr` attribute value of a tag to `literal` which just
returns it.  If the attribute isn't found, or the XML data isn't a
tag, then `none` will discard it.

> showAttr :: String -> CFilter i
> showAttr attr = iffind attr literal none

The Inkscape layers are contained in `<g inkscape:groupmode='layer'
...>` tags.  The name of the layer is in the `inkscape:label`
attribute.  I imagine this will change as Inkscape evolves.  The `o`
is the composition operator for `CFilter`s.

> isLayer = matchAttrString "inkscape:groupmode" "layer"
> getLayerNames = showAttr "inkscape:label" `o` isLayer `o` children

Isolating the layers
--------------------

Again proceeding from the outside of my program inwards, a layer is
isolated with this helper, using `iffind` to match either the layer
name or the layer "Background" which I'm going to leave in all the
output files.  The final `keep` argument to `iffind` says to keep
parts of the XML that don't have the `"inkscape:label"` attribute.

> selectLayer :: String -> Document Posn -> Document Posn
> selectLayer layer doc = onContent "-" (chip (visible `o` onlyLayer)) doc
>     where onlyLayer = iffind "inkscape:label" layerOrBG keep
>           layerOrBG l = if l == layer || l == "Background" then keep else none

In writing `visible` I was surprised that there was a combinator to set
_all_ attributes for a tag, but none to set a single attribute.

> visible = setAttr "style" "display:inline"
> setAttr key val (CElem (Elem tag attrs cs) i) = [CElem (Elem tag newattrs cs) i]
>     where newattrs = (key, AttValue [Left val]) : filter ((/= key) . fst) attrs
> setAttr key val other = [other] -- Hackish?

As I mentioned before, there is no way that I see to directly apply
this filter to an XML file using HaXml.  The type `CFilter = Content
-> [Content]` needs wrapping to apply to an XML `Element` directly.
Notice how I have to pass in a `file` for error reporting; it feels
like I'm doing things I'm not supposed to.

> filterElem :: FilePath -> CFilter Posn -> Element Posn -> [Content Posn]
> filterElem file f e = f (CElem e (posInNewCxt file Nothing))

> xmlElem (Document _ _ e _) = e

And now the function to actually apply a filter to an XML document.
This is straight from the body of `processXmlWith` in the HaXml
source, with `filterElem` pulled out.

> onContent :: FilePath -> (CFilter Posn) -> Document Posn -> Document Posn
> onContent file filter (Document p s e m) =
>     case filterElem file filter e of
>              [CElem e' _] -> Document p s e' m
>              []           -> error "produced no output"
>              _            -> error "produced more than one output"

Bits and pieces
---------------

I also used a modified style for the HughesPJ pretty printer

> xmlStyle = style { mode = LeftMode }

And a big list of slide names, just three digits for this one-off job.  Please
don't make a presentation with more than 999 slides.

> slideNumbers = map (printf "%03d") ([1..999] :: [Int])
> slideNames = map ("Slide"++) slideNumbers

