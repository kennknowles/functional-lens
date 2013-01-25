
I frequently have to "import" data from one database to another in
order to get on with more interesting work, a process
sometimes ingloriously referred to as "ETL: Extract, Transform, Load".
Usually this must be done in some programming language already
established at an organization, such as Python or Scala. However, in
developing a library to do this quickly and fairly declaratively,
I found it useful to write a mostly-undefined prototype in Haskell,
to "type-check" my thoughts. This essay is very much about
databases as they exist in the wild, but
draws quite a bit of
inspiration from the philosophical aspects of Rich Hickey's
[talks](http://www.infoq.com/presentations/Value-Values)
[on](http://www.infoq.com/presentations/Simple-Made-Easy)
[programming](http://www.infoq.com/presentations/Are-We-There-Yet-Rich-Hickey) and
[Datomic / the database as a value](http://www.infoq.com/presentations/Datomic-Database-Value).
There is undoubtedly extensive database theory literature
that would also be helpful; please do point me towards it
in the comments.

Databases, datums, and imports
------------------------------

It is useful to step back to basic principles to model this
scenario sufficiently abstractly. In particular, I want
to have no particular notion of a _database_, except that it
is a place that one stores things one learns.
So I will define abstract types `DB` for storage
and `Datum` for the input.

> import Control.Monad.Reader -- Ignore for now, imports are just required up top
>
> data Datum -- Essentially a row of the source database, if row-based
> data DB    -- The target database

An `Import` is a function that takes just one additional datum and
incorporates all the learned knowledge into the database.

> type Import = Datum -> DB -> DB

Not just any function is suitable to be an `Import`. Learning
from the same datum twice - in this setting - should not result
in more new information. In order words for `f :: Import`
we require that `f` be idempotent.

    f datum == f datum . f datum

Moreover, if we treat the analogy of database contents with
knowledge very strictly, we should be unable to ever
"know" a contradiction. We can add information, but never
remove or change it. This idea is usuall discussed as
the "information ordering" but I will just call it
`<=` where no information (aka `NULL` or ⊥) is less
than any value, and all other values are related
only to each other.

    db <= f datum db

Note that this is stronger than monotonicity, as a constant
function is always monotonic. The best word for this property
in the context of databases is that `f` is _consistent_.

Knowing these properties of an import, I can be assured that it is safe to run
the import on all the data available as many times as I like. The order may
effect how many runs it takes, since we do _not_ require commutativity:

    f datum1 . f datum2 =?= f datum2 . f datum1

However, we can be assured that re-running will eventually hit a
fixed point. In practice, it is usually very easy to order
an import so that a single run suffices, two in more complex
scenarios.

There are two equivalent yet legitimately interesting ways to
think about importing a list of data. The first is the
obvious one: For each piece of data, transform the database
and pass on the result.

> importAll :: Import -> [Datum] -> DB -> DB
> importAll importOne datums db = foldr importOne db datums

The second considers functions `DB -> DB` to be more central, and
does not even bind the variable `db` in its definition:
It first composes all the single transformations into one mondo
transformation, which is then applied to the input database.

> importAll' :: Import -> [Datum] -> DB -> DB
> importAll' importOne datums = foldr (.) id (map importOne datums)


Conclusions, Deductions, and Translations
-----------------------------------------

The above definition is complete and flexible, but there is 
more structure to most databases, hence most imports. To
model the extremely likely scenario that the database has
an atomic element, such as rows for SQL or documents for various
flavors of NoSQL, call these things `Conclusion`s with
a single fundamental operation `save`.

> data Conclusion
>
> save :: Conclusion -> DB -> DB
> save = undefined

With the expected idempotency condition that `save con == save con . save con`.

Now a typical import will consist of drawing some set of `Conclusion`s
for each `Datum` encountered, possibly by combining the datum with
information already stored in the database. For lack of a better
name, I will call this a `Deduction`, and transform it into an `Import`
with the help of `save`.

> type Deduction = Datum -> DB -> [Conclusion]
>
> deduce :: Deduction -> Import
> deduce upsertion datum db = foldr save db (upsertion datum db)

However, it may be that things are even simpler and that
each `Datum` results in a single new `Conclusion`. This is more
the usual notion of a "data import" and means - to stretch an
already thin analogy - that each `Datum` is sort of already
a `Conclusion` but with respect to the wrong context, so
I'll call this a `Translation`.

> type Translation = Datum -> DB -> Conclusion
>
> translate :: Translation -> Import
> translate trans datum db = save (trans datum db) db

However, there is a major problem: Neither `translate` nor `deduce`
result in consistent imports, because multiple `Datum`s may result
in the a `Conclusion` with the same primary key but different
attributes. This is almost never desirable; when two translations
or deductions emit a conclusion with the same primary key, it is
intended to be consistent with the database, i.e. they should
only emit conclusions `con` such that `save con` is consistent

    db <= save con db

In normal database parlance, this is like an "upsert" except on
all attributes as well. At the level of rows or documents,
we must first fetch the document that would be created, and
then modify it according to the new conclusion. Any
conflicting attributes is an error (hacks excepted, of course).
I will break these apart into `Lookup` and `Augment`,
which are then recombined in the brilliantly named
`lookupAndAugment`.
 
> type Lookup = Datum -> DB -> Conclusion
> type Augment = Datum -> DB -> Conclusion -> Conclusion
>
> lookupAndAugment :: Lookup -> Augment -> Translation
> lookupAndAugment lookup augment datum db = augment datum db (lookup datum db)

One could implement `lookupAndAugment` to enforce that the output
conclusion is consistent with the input. [^debug]

[^debug]: In a test-edit-debug cycle, you'll need a way to turn
          off consistency checking, unless you snapshot
          and reset the target database with each run. A good idea, but
          slow, and it is usually fine to operate on a test database
          and just mutate it repeatedly.


Making it imperative
--------------------

To get a step closer to the imperative scripting that this prototype
targets, this section adjusts the definitions above to stop
passing the database around quite so much.

A first step is to note that the database is "always there" as
part of the environment, which is exactly what the `Reader`
monad represents. Here are all of the above definitions rewritten
without ever taking the database as input.

> type Import' = Datum -> Reader DB DB
> type Translation' = Datum -> Reader DB Conclusion
> type Lookup' = Translation'
> type Augment' = Datum -> Reader DB (Conclusion -> Conclusion)
>
> save' :: Conclusion -> Reader DB DB
> save' = undefined
>
> translate' :: Translation' -> Import'
> translate' trans datum = do db <- ask
>                             conclusion <- trans datum
>                             save' conclusion
>
> lookupAndAugment' :: Lookup' -> Augment' -> Translation'
> lookupAndAugment' lookup augment datum = do current <- lookup datum
>                                             improvements <- augment datum
>                                             return (improvements current)

The next and final step is to stop returning the database, but mutate it
in place, by replacing `Reader DB` with `IO` and `DB` with `()`.

> type Import'' = Datum -> IO ()
> type Translation'' = Datum -> IO Conclusion
> type Lookup'' = Translation''
> type Augment'' = Datum -> IO (Conclusion -> Conclusion)
>
> save'' :: Conclusion -> IO ()
> save'' = undefined
> 
> translate'' :: Translation'' -> Import''
> translate'' trans datum = do conclusion <- trans datum
>                              save'' conclusion
>
> lookupAndAugment'' :: Lookup'' -> Augment'' -> Translation''
> lookupAndAugment'' lookup augment datum = do current <- lookup datum
>                                              improvements <- augment datum
>                                              return (improvements current)
>

And it is nice to see that moving from `Reader DB` to `IO` does not
change the text of `lookupAndAugment`, so I have some confidence
that it is a canonical definition.

That's it! Just a bit of how I do typed functional prototyping before committing
to the task of implementing in a lower-level scripting language.
