{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 1  VECTORS AND FRIENDS (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- NOTE (19/9/17) This file is currently incomplete: more will arrive on
-- GitHub.

-- MARK SCHEME (transcribed from paper): the (m) numbers add up to slightly
-- more than 25, so should be taken as the maximum number of marks losable on
-- the exercise. In fact, I did mark it negatively, but mostly because it was
-- done so well (with Agda's help) that it was easier to find the errors.


------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude


------------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 4 _,-_   -- the "cons" operator associates to the right

-- I like to use the asymmetric ,- to remind myself that the element is to
-- the left and the rest of the list is to the right.

-- Vectors are useful when there are important length-related safety
-- properties.


------------------------------------------------------------------------------
-- Heads and Tails
------------------------------------------------------------------------------

-- We can rule out nasty head and tail errors by insisting on nonemptiness!

--??--1.1-(2)-----------------------------------------------------------------

vHead : {X : Set}{n : Nat} -> Vec X (suc n) -> X
vHead xs = {!!}

vTail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
vTail xs = {!!}

vHeadTailFact :  {X : Set}{n : Nat}(xs : Vec X (suc n)) ->
                 (vHead xs ,- vTail xs) == xs
vHeadTailFact xs = {!!}                 

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Concatenation and its Inverse
------------------------------------------------------------------------------

--??--1.2-(2)-----------------------------------------------------------------

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
xs +V ys = {!!}
infixr 4 _+V_

vChop : {X : Set}(m : Nat){n : Nat} -> Vec X (m +N n) -> Vec X m * Vec X n
vChop m xs = {!!}

vChopAppendFact : {X : Set}{m n : Nat}(xs : Vec X m)(ys : Vec X n) ->
                  vChop m (xs +V ys) == (xs , ys)
vChopAppendFact xs ys = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Map, take I
------------------------------------------------------------------------------

-- Implement the higher-order function that takes an operation on
-- elements and does it to each element of a vector. Use recursion
-- on the vector.
-- Note that the type tells you the size remains the same.

-- Show that if the elementwise function "does nothing", neither does
-- its vMap. "map of identity is identity"

-- Show that two vMaps in a row can be collapsed to just one, or
-- "composition of maps is map of compositions"

--??--1.3-(2)-----------------------------------------------------------------

vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vMap f xs = {!!}

vMapIdFact : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
             {n : Nat}(xs : Vec X n) -> vMap f xs == xs
vMapIdFact feq xs = {!!}

vMapCpFact : {X Y Z : Set}{f : Y -> Z}{g : X -> Y}{h : X -> Z}
               (heq : (x : X) -> f (g x) == h x) ->
             {n : Nat}(xs : Vec X n) ->
               vMap f (vMap g xs) == vMap h xs
vMapCpFact heq xs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- vMap and +V
------------------------------------------------------------------------------

-- Show that if you've got two vectors of Xs and a function from X to Y,
-- and you want to concatenate and map, it doesn't matter which you do
-- first.

--??--1.4-(1)-----------------------------------------------------------------

vMap+VFact : {X Y : Set}(f : X -> Y) ->
             {m n : Nat}(xs : Vec X m)(xs' : Vec X n) ->
             vMap f (xs +V xs') == (vMap f xs +V vMap f xs')
vMap+VFact f xs xs' = {!!}

--??--------------------------------------------------------------------------

-- Think about what you could prove, relating vMap with vHead, vTail, vChop...
-- Now google "Philip Wadler" "Theorems for Free"


------------------------------------------------------------------------------
-- Applicative Structure (giving mapping and zipping cheaply)
------------------------------------------------------------------------------

--??--1.5-(2)-----------------------------------------------------------------

-- HINT: you will need to override the default invisibility of n to do this.
vPure : {X : Set} -> X -> {n : Nat} -> Vec X n
vPure x {n} = {!!}

_$V_ : {X Y : Set}{n : Nat} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
fs $V xs = {!!}
infixl 3 _$V_  -- "Application associates to the left,
               --  rather as we all did in the sixties." (Roger Hindley)

-- Pattern matching and recursion are forbidden for the next two tasks.

-- implement vMap again, but as a one-liner
vec : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vec f xs = {!!}

-- implement the operation which pairs up corresponding elements
vZip : {X Y : Set}{n : Nat} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vZip xs ys = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Applicative Laws
------------------------------------------------------------------------------

-- According to "Applicative programming with effects" by
--   Conor McBride and Ross Paterson
-- some laws should hold for applicative functors.
-- Check that this is the case.

--??--1.6-(2)-----------------------------------------------------------------

vIdentity : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
            {n : Nat}(xs : Vec X n) -> (vPure f $V xs) == xs
vIdentity feq xs = {!!}

vHomomorphism : {X Y : Set}(f : X -> Y)(x : X) ->
                {n : Nat} -> (vPure f $V vPure x) == vPure (f x) {n}
vHomomorphism f x {n} = {!!}

vInterchange : {X Y : Set}{n : Nat}(fs : Vec (X -> Y) n)(x : X) ->
               (fs $V vPure x) == (vPure (_$ x) $V fs)
vInterchange fs x = {!!}

vComposition : {X Y Z : Set}{n : Nat}
               (fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
               (vPure _<<_ $V fs $V gs $V xs) == (fs $V (gs $V xs))
vComposition fs gs xs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings (also known in the business as "thinnings")
------------------------------------------------------------------------------

-- What have these to do with Pascal's Triangle?

data _<=_ : Nat -> Nat -> Set where
  oz :                          zero  <= zero
  os : {n m : Nat} -> n <= m -> suc n <= suc m
  o' : {n m : Nat} -> n <= m ->     n <= suc m

-- Find all the values in each of the following <= types.
-- This is a good opportunity to learn to use C-c C-a with the -l option
--   (a.k.a. "google the type" without "I feel lucky")
-- The -s n option also helps.

--??--1.7-(1)-----------------------------------------------------------------

all0<=4 : Vec (0 <= 4) {!!}
all0<=4 = {!!}

all1<=4 : Vec (1 <= 4) {!!}
all1<=4 = {!!}

all2<=4 : Vec (2 <= 4) {!!}
all2<=4 = {!!}
       
all3<=4 : Vec (3 <= 4) {!!}
all3<=4 = {!!}

all4<=4 : Vec (4 <= 4) {!!}
all4<=4 = {!!}

-- Prove the following. A massive case analysis "rant" is fine.

no5<=4 : 5 <= 4 -> Zero
no5<=4 th = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings Select From Vectors
------------------------------------------------------------------------------

-- Use n <= m to encode the choice of n elements from an m-Vector.
-- The os constructor tells you to take the next element of the vector;
-- the o' constructor tells you to omit the next element of the vector.

--??--1.8-(2)-----------------------------------------------------------------

_<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m
                     -> Vec X n
th <?= xs = {!!}

-- it shouldn't matter whether you map then select or select then map

vMap<?=Fact : {X Y : Set}(f : X -> Y)
              {n m : Nat}(th : n <= m)(xs : Vec X m) ->
              vMap f (th <?= xs) == (th <?= vMap f xs)
vMap<?=Fact f th xs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Our Favourite Thinnings
------------------------------------------------------------------------------

-- Construct the identity thinning and the empty thinning.

--??--1.9-(1)-----------------------------------------------------------------

oi : {n : Nat} -> n <= n
oi {n}  = {!!}

oe : {n : Nat} -> 0 <= n
oe {n}  = {!!}

--??--------------------------------------------------------------------------


-- Show that all empty thinnings are equal to yours.

--??--1.10-(1)----------------------------------------------------------------

oeUnique : {n : Nat}(th : 0 <= n) -> th == oe
oeUnique i = {!!}

--??--------------------------------------------------------------------------


-- Show that there are no thinnings of form big <= small  (TRICKY)
-- Then show that all the identity thinnings are equal to yours.
-- Note that you can try the second even if you haven't finished the first.
-- HINT: you WILL need to expose the invisible numbers.
-- HINT: check CS410-Prelude for a reminder of >=

--??--1.11-(3)----------------------------------------------------------------

oTooBig : {n m : Nat} -> n >= m -> suc n <= m -> Zero
oTooBig {n} {m} n>=m th = {!!}

oiUnique : {n : Nat}(th : n <= n) -> th == oi
oiUnique th = {!!}

--??--------------------------------------------------------------------------


-- Show that the identity thinning selects the whole vector

--??--1.12-(1)----------------------------------------------------------------

id-<?= : {X : Set}{n : Nat}(xs : Vec X n) -> (oi <?= xs) == xs
id-<?= xs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Composition of Thinnings
------------------------------------------------------------------------------

-- Define the composition of thinnings and show that selecting by a
-- composite thinning is like selecting then selecting again.
-- A small bonus applies to minimizing the length of the proof.
-- To collect the bonus, you will need to think carefully about
-- how to make the composition as *lazy* as possible.

--??--1.13-(3)----------------------------------------------------------------

_o>>_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
th o>> th' = {!!}

cp-<?= : {p n m : Nat}(th : p <= n)(th' : n <= m) ->
         {X : Set}(xs : Vec X m) ->
         ((th o>> th') <?= xs) == (th <?= (th' <?= xs))
cp-<?= th th' xs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Thinning Dominoes
------------------------------------------------------------------------------

--??--1.14-(3)----------------------------------------------------------------

idThen-o>> : {n m : Nat}(th : n <= m) -> (oi o>> th) == th
idThen-o>> th = {!!}

idAfter-o>> : {n m : Nat}(th : n <= m) -> (th o>> oi) == th
idAfter-o>> th = {!!}

assoc-o>> : {q p n m : Nat}(th0 : q <= p)(th1 : p <= n)(th2 : n <= m) ->
            ((th0 o>> th1) o>> th2) == (th0 o>> (th1 o>> th2))
assoc-o>> th0 th1 th2 = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Vectors as Arrays
------------------------------------------------------------------------------

-- We can use 1 <= n as the type of bounded indices into a vector and do
-- a kind of "array projection". First we select a 1-element vector from
-- the n-element vector, then we take its head to get the element out.

vProject : {n : Nat}{X : Set} -> Vec X n -> 1 <= n -> X
vProject xs i = vHead (i <?= xs)

-- Your (TRICKY) mission is to reverse the process, tabulating a function
-- from indices as a vector. Then show that these operations are inverses.

--??--1.15-(3)----------------------------------------------------------------

-- HINT: composition of functions
vTabulate : {n : Nat}{X : Set} -> (1 <= n -> X) -> Vec X n
vTabulate {n} f = {!!}

-- This should be easy if vTabulate is correct.
vTabulateProjections : {n : Nat}{X : Set}(xs : Vec X n) ->
                       vTabulate (vProject xs) == xs
vTabulateProjections xs = {!!}

-- HINT: oeUnique
vProjectFromTable : {n : Nat}{X : Set}(f : 1 <= n -> X)(i : 1 <= n) ->
                    vProject (vTabulate f) i == f i
vProjectFromTable f i = {!!}

--??--------------------------------------------------------------------------
