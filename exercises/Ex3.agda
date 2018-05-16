{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise
{-# OPTIONS --allow-unsolved-metas #-}  -- allows import, unfinished

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 3  WINDOWS AND OTHER STORIES (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Categories
open import Ex2


------------------------------------------------------------------------------
--  PART I:  Splittings
------------------------------------------------------------------------------

-- The type    ls <[ ms ]> rs
-- is similar to that found in Lec2.agda, but it works on lists, not numbers.
-- It provides the evidence that a list ms can be split into a left sublist ls
-- and a right sublist rs. In effect, it's a vector of bits that say which
-- elements of ms go left and which go right.

data _<[_]>_ {X : Set} : List X -> List X -> List X -> Set where
  sz : [] <[ [] ]> []
  sl : forall {l ls ms rs} -> ls <[ ms ]> rs -> (l ,- ls) <[ l ,- ms ]> rs
  sr : forall {r ls ms rs} -> ls <[ ms ]> rs -> ls <[ r ,- ms ]> (r ,- rs)


--??--3.1-(4)-----------------------------------------------------------------

-- Adapt _>[_]<_ from Lec2 to work for All. Given a P for each element of
-- ls and rs, riffle them together to get Ps for all the ms.

_>[_]<_ : {X : Set}{ls ms rs : List X} -> {P : X -> Set} ->
          All P ls -> ls <[ ms ]> rs -> All P rs ->
          All P ms
pl >[ s ]< pr = {!!}

-- Now, buikd the view that shows riffling can be inverted, using a splitting
-- as the instructions to discover how to split an All in two.

data IsRiffle {X : Set}{ls ms rs : List X}(s : ls <[ ms ]> rs){P : X -> Set}
  : All P ms -> Set where
  mkRiffle : (pl : All P ls)(pr : All P rs) -> IsRiffle s (pl >[ s ]< pr)
  
isRiffle : {X : Set}{ls ms rs : List X}(s : ls <[ ms ]> rs)
           {P : X -> Set}(pm : All P ms) -> IsRiffle s pm
isRiffle s pm = {!!}

--??--------------------------------------------------------------------------


--??--3.2-(4)-----------------------------------------------------------------

-- Construct the "all on the right" splitting.

srs : forall {X : Set}{xs : List X} -> [] <[ xs ]> xs
srs = {!!}

-- Construct a view to show that any "none on the left" splitting is
-- "all on the right". Come up with the type yourself.


-- Construct the splitting that corresponds to concatenation.

slrs : forall {X : Set}(xs ys : List X) -> xs <[ xs +L ys ]> ys
slrs xs ys = {!!}

--??--------------------------------------------------------------------------

--??--3.3-(4)-----------------------------------------------------------------

-- Invent other useful operations which transform splittings.
-- You will need some to do later parts of the exercise, so maybe
-- wait until you see what you need.

-- I expect you will need at least something that takes a pair of splittings
-- that make a tree, like
--
--                  ms
--               <[    ]>
--            ls          rs
--                     <[    ]>
--                 lrs          rrs
--
-- and compute a "rotated" pair of splittings like
--
--                  ms
--               <[    ]>
--            ??          rrs
--         <[    ]>
--      ls          lrs

-- HINT: Sg is your friend

-- You'll probably need some other stuff, too.

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
--  PART II:  Permutations
------------------------------------------------------------------------------

-- When is one list a permutation of another?

data _~_ {X : Set} : List X -> List X -> Set where

  -- [] is a permutation of []
  []   : [] ~ []

  -- if xs ~ ys, then (x ,- xs) is a permutation of any list made by
  -- shoving x somewhere into ys
  _,-_ : forall {x xs ys' ys} ->
           (x ,- []) <[ ys' ]> ys ->
           xs ~ ys ->
           (x ,- xs) ~ ys'


--??--3.4-(1)-----------------------------------------------------------------

-- Show that every list is a permutation of itself.

reflP : {X : Set}{xs : List X} -> xs ~ xs
reflP = {!!}

--??--------------------------------------------------------------------------


--??--3.5-(5)-----------------------------------------------------------------

-- Construct an "unbiased" insertion operator which lets you grow a
-- permutation by inserting a new element anywhere, left and right

insP : forall {X : Set}{z : X}{xs xs' ys ys'} ->
         (z ,- []) <[ xs' ]> xs ->
         (z ,- []) <[ ys' ]> ys ->
         xs ~ ys -> xs' ~ ys'
insP l r p = {!!}

-- Now show that, given a permutation, and any element on the left,
-- you can find out where it ended up on the right, and why the
-- remaining elements form a permutation.

findLonR : forall {X : Set}{z : X}{xs xs' ys'} ->
                  (z ,- []) <[ xs' ]> xs ->
                  xs' ~ ys' ->
                  {!!}
findLonR l p = {!!}

-- HINT: again, you may need Sg to give a sensible return type.

--??--------------------------------------------------------------------------


--??--3.6-(5)-----------------------------------------------------------------

-- Show that permutation is transitive.

transP : {X : Set}{xs ys zs : List X} -> xs ~ ys -> ys ~ zs -> xs ~ zs
transP p q = {!!}

-- HINT: you will need to define some useful operations on splittings to
-- get this to work.

-- HINT: this may help you figure out what you need for findLonR

-- For a small bonus, show that permutations are the morphisms of a
-- Category.

-- Show that permutation is symmetric.

symP : {X : Set}{xs ys : List X} -> xs ~ ys -> ys ~ xs
symP p = {!!}

-- A category where all morphisms are invertible is called a "groupoid".

--??--------------------------------------------------------------------------


--??--3.7-(2)-----------------------------------------------------------------

-- Make permutations act on All.

permute : {X : Set}{xs ys : List X} -> xs ~ ys ->
          {Q : X -> Set} -> All Q xs -> All Q ys

permute p qs = {!!}

--??--------------------------------------------------------------------------



-- MORE TO FOLLOW

-- AGAIN, "MORE" BECAME CLEARLY SURPLUS TO REQUIREMENTS
