{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise
{-# OPTIONS --allow-unsolved-metas #-}  -- allows import, unfinished

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 2  CATEGORIES AND MONADS (worth 50%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- NOTE (19/10/17)  This file is currently incomplete: more will arrive on
-- GitHub.

-- NOTE (29/10/17)  All components are now present.

-- REFLECTION: When I started setting this exercise, I intended it as a
-- normal size 25% exercise, but it grew and grew, as did the struggles of
-- the students. I accepted that I had basically set two exercises in one
-- file and revalued it as such.


------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Categories
open import Ex1


------------------------------------------------------------------------------
-- Categorical Jigsaws (based on Ex1)
------------------------------------------------------------------------------

-- In this section, most of the work has already happened. All you have to do
-- is assemble the collection of things you did into Ex1 into neat categorical
-- packaging.

--??--2.1-(4)-----------------------------------------------------------------

OPE : Category            -- The category of order-preserving embeddings...
OPE = record
  { Obj          = Nat    -- ...has numbers as objects...
  ; _~>_         = _<=_   -- ...and "thinnings" as arrows.
                          -- Now, assemble the rest of the components.
  ; id~>         = {!!}
  ; _>~>_        = {!!}
  ; law-id~>>~>  = {!!}
  ; law->~>id~>  = {!!}
  ; law->~>>~>   = {!!}
  }

VEC : Nat -> SET => SET                -- Vectors of length n...
VEC n = record
  { F-Obj       = \ X -> Vec X n       -- ...give a functor from SET to SET...
  ; F-map       = \ f xs -> vMap f xs  -- ...doing vMap to arrows.
                                       -- Now prove the laws.
  ; F-map-id~>  = extensionality \ xs -> {!!}
  ; F-map->~>   = \ f g -> extensionality \ xs -> {!!}
  }

Op : Category -> Category             -- Every category has an opposite...
Op C = record
  { Obj          = Obj                -- ...with the same objects, but...  
  ; _~>_         = \ S T -> T ~> S    -- ...arrows that go backwards!
                                      -- Now, find the rest!
  ; id~>         = {!!}
  ; _>~>_        = {!!}
  ; law-id~>>~>  = {!!}
  ; law->~>id~>  = {!!}
  ; law->~>>~>   = {!!}
  } where open Category C

CHOOSE : Set -> OPE => Op SET    -- Show that thinnings from n to m...
CHOOSE X = record                -- ...act by selection...
  { F-Obj       = Vec X          -- ...to cut vectors down from m to n.
  ; F-map       = {!!}
  ; F-map-id~>  = extensionality {!!}
  ; F-map->~>   = \ f g -> extensionality {!!}
  }

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- The List Monad (a warm-up)
------------------------------------------------------------------------------

-- The declaration of List has been added to the CS410-Prelude file:

-- data List (X : Set) : Set where
--   []   : List X
--   _,-_ : (x : X)(xs : List X) -> List X
-- infixr 4 _,-_

-- Appending two lists is rather well known, so I'll not ask you to write it.

_+L_ : {X : Set} -> List X -> List X -> List X
[]        +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
infixr 4 _+L_

-- But I will ask you to find some structure for it.


--??--2.2-(3)-----------------------------------------------------------------

LIST-MONOID : Set -> Category
LIST-MONOID X =            -- Show that _+L_ is the operation of a monoid,...
  record
  { Obj          = One     -- ... i.e., a category with one object.
  ; _~>_         = {!!}
  ; id~>         = {!!}
  ; _>~>_        = {!!}
  ; law-id~>>~>  = {!!}
  ; law->~>id~>  = {!!}
  ; law->~>>~>   = {!!}
  } where
  -- useful helper proofs (lemmas) go here

--??--------------------------------------------------------------------------

-- Next, functoriality of lists. Given a function on elements, show how to
-- apply that function to all the elements of a list. (Haskell calls this
-- operation "map".)

--??--2.3-(3)-----------------------------------------------------------------

list : {X Y : Set} -> (X -> Y) -> List X -> List Y
list f xs = {!!}

LIST : SET => SET
LIST = record
  { F-Obj       = List
  ; F-map       = list
  ; F-map-id~>  = extensionality {!!}
  ; F-map->~>   = \ f g -> extensionality {!!}
  } where
  -- useful helper proofs (lemmas) go here

--??--------------------------------------------------------------------------


-- Moreover, applying a function elementwise should respect appending.

--??--2.4-(3)-----------------------------------------------------------------

LIST+L : {X Y : Set}(f : X -> Y) -> LIST-MONOID X => LIST-MONOID Y
LIST+L {X}{Y} f = record
  { F-Obj       = id
  ; F-map       = list f -- this yellow will go once LIST-MONOID has arrows!
  ; F-map-id~>  = {!!}
  ; F-map->~>   = {!!}
  } where
  -- useful helper proofs (lemmas) go here


--??--------------------------------------------------------------------------


-- Next, we have two very important "natural transformations".

--??--2.5-(1)-----------------------------------------------------------------

SINGLE : ID ~~> LIST
SINGLE = record
  { xf          = \ x -> x ,- []      -- turn a value into a singleton list
  ; naturality  = \ f -> {!!}
  }

--??--------------------------------------------------------------------------

-- Here, naturality means that it doesn't matter
-- whether you apply a function f, then make a singleton list
-- or you make a singleton list, then apply f to all (one of) its elements.


-- Now, define the operation that concatenates a whole list of lists, and
-- show that it, too, is natural. That is, it doesn't matter whether you
-- transform the elements (two layers inside) then concatenate, or you
-- concatenate, then transform the elements.

--??--2.6-(3)-----------------------------------------------------------------

concat : {X : Set} -> List (List X) -> List X
concat xss = {!!}

CONCAT : (LIST >=> LIST) ~~> LIST
CONCAT = record
  { xf          = concat
  ; naturality  = {!!}
  } where
  -- useful helper proofs (lemmas) go here

--??--------------------------------------------------------------------------


-- You've nearly built your first monad! You just need to prove that
-- single and concat play nicely with each other.

--??--2.7-(4)-----------------------------------------------------------------

module LIST-MONAD where
  open MONAD LIST public
  ListMonad : Monad
  ListMonad = record
    { unit      = SINGLE
    ; mult      = CONCAT
    ; unitMult  = {!!}
    ; multUnit  = {!!}
    ; multMult  = {!!}
    } where
    -- useful helper proofs (lemmas) go here

-- open LIST-MONAD

--??--------------------------------------------------------------------------

-- More monads to come...


------------------------------------------------------------------------------
-- Categories of Indexed Sets
------------------------------------------------------------------------------

-- We can think of some
--   P : I -> Set
-- as a collection of sets indexed by I, such that
--   P i
-- means "exactly the P-things which fit with i".

-- You've met
--   Vec X : Nat -> Set
-- where
--   Vec X n
-- means "exactly the vectors which fit with n".

-- Now, given two such collections, S and T, we can make a collection
-- of function types: the functions which fit with i map the
-- S-things which fit with i to the T-things which fit with i.

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i

-- So, (Vec X -:> Vec Y) n contains the functions which turn
-- n Xs into n Ys.

-- Next, if we know such a collection of sets, we can claim to have
-- one for each index.

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i    -- [_] {I} P = (i : I) -> P i

-- E.g., [ Vec X -:> Vec Y ] is the type of functions from X-vectors
-- to Y-vectors which preserve length.

-- For any such I, we get a category of indexed sets with index-preserving
-- functions.

_->SET : Set -> Category
I ->SET = record
  { Obj    = I -> Set                 -- I-indexed sets
  ; _~>_   = \ S T -> [ S -:> T ]     -- index-respecting functions
  ; id~>   = \ i -> id                -- the identity at every index
  ; _>~>_  = \ f g i -> f i >> g i    -- composition at every index
  ; law-id~>>~> = refl                -- and the laws are very boring
  ; law->~>id~> = refl
  ; law->~>>~>  = \ f g h -> refl _
  }

-- In fact, we didn't need to choose SET here. We could do this construction
-- for any category: index the objects; index the morphisms.
-- But SET is plenty to be getting on with.

-- Now, let me define an operation that makes types from lists.

All : {X : Set} -> (X -> Set) -> (List X -> Set)
All P [] = One
All P (x ,- xs) = P x * All P xs

-- The idea is that we get a tuple of P-things: one for each list element.
-- So
--     All P (1 ,- 2 ,- 3 ,- [])
--   = P 1 * P 2 * P 3 * One

-- Note that if you think of List One as a version of Nat,
-- All becomes a lot like Vec.

copy : Nat -> List One
copy zero = []
copy (suc n) = <> ,- copy n

VecCopy : Set -> Nat -> Set
VecCopy X n = All (\ _ -> X) (copy n)

-- Now, your turn...

--??--2.8-(4)-----------------------------------------------------------------

-- Show that, for any X, All induces a functor
-- from (X ->SET) to (List X ->SET)

all : {X : Set}{S T : X -> Set} ->
      [ S -:> T ] -> [ All S -:> All T ]
all f xs ss = {!!}

ALL : (X : Set) -> (X ->SET) => (List X ->SET)
ALL X = record
  { F-Obj      = All
  ; F-map      = all
  ; F-map-id~> = {!!}
  ; F-map->~>  = {!!}
  } where
  -- useful helper facts go here

--??--------------------------------------------------------------------------


-- ABOVE THIS LINE, 25%
-- BELOW THIS LINE, 25%


------------------------------------------------------------------------------
-- Cutting Things Up
------------------------------------------------------------------------------

-- Next, we're going to develop a very general technique for building
-- data structures.

-- We may think of an I |> O as a way to "cut O-shapes into I-shaped pieces".
-- The pointy end points to the type being cut; the flat end to the type of
-- pieces.

record _|>_ (I O : Set) : Set where
  field
    Cuts   : O -> Set                      -- given o : O, how may we cut it?
    inners : {o : O} -> Cuts o -> List I   -- given how we cut it, what are
                                           --   the shapes of its pieces?

-- Let us have some examples right away!

VecCut : One |> Nat              -- cut numbers into boring pieces
VecCut = record
  { Cuts = \ n -> One            -- there is one way to cut n
  ; inners = \ {n} _ -> copy n   -- and you get n pieces
  }

-- Here's a less boring example. You can cut a number into *two* pieces
-- by finding two numbers that add to it.

NatCut : Nat |> Nat
NatCut = record
  { Cuts = \ mn -> Sg Nat \ m -> Sg Nat \ n -> (m +N n) == mn
  ; inners = \ { (m , n , _) -> m ,- n ,- [] }
  }

-- The point is that we can make data structures that record how we
-- built an O-shaped thing from I-shaped pieces.

record Cutting {I O}(C : I |> O)(P : I -> Set)(o : O) : Set where
  constructor _8><_               -- "scissors"
  open _|>_ C
  field
    cut     : Cuts o              -- we decide how to cut o
    pieces  : All P (inners cut)  -- then we give all the pieces.
infixr 3 _8><_

-- For example...

VecCutting : Set -> Nat -> Set
VecCutting X = Cutting VecCut (\ _ -> X)

myVecCutting : VecCutting Char 5
myVecCutting = <> 8>< 'h' , 'e' , 'l' , 'l' , 'o' , <>

-- Or, if you let me fiddle about with strings for a moment,...
length : {X : Set} -> List X -> Nat
length [] = zero
length (x ,- xs) = suc (length xs)

listVec : {X : Set}(xs : List X) -> Vec X (length xs)
listVec [] = []
listVec (x ,- xs) = x ,- listVec xs

strVec : (s : String) -> Vec Char (length (primStringToList s))
strVec s = listVec (primStringToList s)

-- ...an example of cutting a number in two, with vector pieces.

footprints : Cutting NatCut (Vec Char) 10
footprints = (4 , 6 , refl 10) 8>< strVec "foot"
                                 , strVec "prints"
                                 , <>

-- Now, let me direct you to the =$ operator, now in CS410-Prelude.agda,
-- which you may find helps with the proofs in the following.

--??--2.9-(3)-----------------------------------------------------------------

-- Using what you already built for ALL, show that every Cutting C gives us
-- a functor between categories of indexed sets.

CUTTING : {I O : Set}(C : I |> O) -> (I ->SET) => (O ->SET)
CUTTING {I}{O} C = record
  { F-Obj = Cutting C
  ; F-map = {!!}
  ; F-map-id~> = extensionality \ o -> extensionality \ { (c 8>< ps) ->
     {!!} }
  ; F-map->~> = \ f g ->
     extensionality \ o -> extensionality \ { (c 8>< ps) ->
     {!!} } 
  } where
  open _|>_ C
  open _=>_ (ALL I)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Interiors
------------------------------------------------------------------------------

-- Next, let me define the notion of an algebra for a given functor in C => C

module ALGEBRA {C : Category}(F : C => C) where
  open Category C
  open _=>_ F

  Algebra : (X : Obj) -> Set   -- we call X the "carrier" of the algebra...
  Algebra X = F-Obj X ~> X     -- ...and we explain how to turn a bunch of Xs
                               -- into one
open ALGEBRA

-- Some week, we'll build categories whose objects are algebras. Not this week.

-- Instead, let's work with them a bit.

-- If we know a way to cut I-shapes into I-shaped pieces, we can build the
-- ways to "tile" an I with I-shaped T-tiles.

data Interior {I}(C : I |> I)(T : I -> Set)(i : I) : Set where
                                         -- either...
  tile : T i -> Interior C T i           -- we have a tile that fits, or...
  <_>  : Cutting C (Interior C T) i ->   -- ...we cut, then tile the pieces.
         Interior C T i

-- Let me give you an example of an interior.

subbookkeeper : Interior NatCut (Vec Char) 13
subbookkeeper = < (3 , 10 , refl _)
                  8>< tile (strVec "sub")
                    , < (4 , 6 , refl _)
                        8>< tile (strVec "book")
                          , tile (strVec "keeper")
                          , <> >
                    , <> >

-- We make a 13-interior from
-- a 3-tile and a 10-interior made from a 4-tile and a 6-tile.

-- Guess what? Interior C is always a Monad! We'll get there.

module INTERIOR {I : Set}{C : I |> I} where  -- fix some C...

  open _|>_ C                                -- ...and open it
  
  open module I->SET {I : Set} = Category (I ->SET)  -- work in I ->SET

  -- tile gives us an arrow from T into Interior C T

  tile' : {T : I -> Set} -> [ T -:> Interior C T ]
  tile' i = tile

  -- <_> gives us an algebra!

  cut' : {T : I -> Set} -> Algebra (CUTTING C) (Interior C T)
  cut' i = <_>

  -- Now, other (CUTTING C) algebras give us operators on interiors.

  module INTERIORFOLD {P Q : I -> Set} where
  
    interiorFold :
      [ P -:> Q ] ->              -- if we can turn a P into a Q...
      Algebra (CUTTING C) Q ->    -- ...and a bunch of Qs into a Q...
      [ Interior C P -:> Q ]      -- ...we can turn an interior of Ps into a Q

    allInteriorFold :             -- annoyingly, we'll need a specialized "all"
      [ P -:> Q ] ->
      Algebra (CUTTING C) Q ->
      [ All (Interior C P) -:> All Q ]

    interiorFold pq qalg i (tile p)      = pq i p
    interiorFold pq qalg i < c 8>< pis > =
      qalg i (c 8>< allInteriorFold pq qalg (inners c) pis)

    -- recursively turn all the sub-interiors into Qs
    allInteriorFold pq qalg []        <>         = <>
    allInteriorFold pq qalg (i ,- is) (pi , pis) =
      interiorFold pq qalg i pi , allInteriorFold pq qalg is pis

    -- The trouble is that if you use
    --   all (interiorFold pq qalg)
    -- to process the sub-interiors, the termination checker complains.

    -- But if you've built "all" correctly, you should be able to prove this:

--??--2.10-(2)----------------------------------------------------------------

    allInteriorFoldLaw : (pq : [ P -:> Q ])(qalg : Algebra (CUTTING C) Q) ->
      allInteriorFold pq qalg == all (interiorFold pq qalg)
    allInteriorFoldLaw pq qalg = extensionality \ is -> extensionality \ ps ->
      {!!}
      where
      -- helper lemmas go here

--??--------------------------------------------------------------------------

    -- Now, do me a favour and prove this extremely useful fact.
    -- Its purpose is to bottle the inductive proof method for functions
    -- built with interiorFold.

--??--2.11-(3)----------------------------------------------------------------

    interiorFoldLemma :
      (pq : [ P -:> Q ])(qalg : Algebra (CUTTING C) Q)
      (f : [ Interior C P -:> Q ]) ->
      ((i : I)(p : P i) -> pq i p == f i (tile p)) ->
      ((i : I)(c : Cuts i)(ps : All (Interior C P) (inners c)) ->
        qalg i (c 8>< all f (inners c) ps) == f i < c 8>< ps >) ->
      (i : I)(pi : Interior C P i) -> interiorFold pq qalg i pi == f i pi

    interiorFoldLemma pq qalg f base step i pi = {!!}

--??--------------------------------------------------------------------------

    -- We'll use it in this form:

    interiorFoldLaw : (pq : [ P -:> Q ])(qalg : Algebra (CUTTING C) Q)
      (f : [ Interior C P -:> Q ]) ->
      ((i : I)(p : P i) -> pq i p == f i (tile p)) ->
      ((i : I)(c : Cuts i)(ps : All (Interior C P) (inners c)) ->
        qalg i (c 8>< all f (inners c) ps) == f i < c 8>< ps >) ->
      interiorFold pq qalg == f
      
    interiorFoldLaw pq qalg f base step =
      extensionality \ i -> extensionality \ pi ->
      interiorFoldLemma pq qalg f base step i pi

  open INTERIORFOLD

  -- Let me pay you back immediately!
  -- An interiorBind is an interiorFold which computes an Interior,
  --   rewrapping each layer with < ... >

  interiorBind : {X Y : I -> Set} ->
                 [ X -:> Interior C Y ] -> [ Interior C X -:> Interior C Y ]
  interiorBind f = interiorFold f (\ i -> <_>)

  -- Because an interiorBind *makes* an interior, we can say something useful
  -- about what happens if we follow it with an interiorFold.

  interiorBindFusion : {X Y Z : I -> Set} ->
    (f : [ X -:> Interior C Y ])
    (yz : [ Y -:> Z ])(zalg : Algebra (CUTTING C) Z) ->
    (interiorBind f >~> interiorFold yz zalg) ==
      interiorFold (f >~> interiorFold yz zalg) zalg

  -- That is, we can "fuse" the two together, making one interiorFold.

  -- I'll do the proof as it's a bit hairy. You've given me all I need.
  -- Note that I don't use extensionality, just laws that relate functions.

  interiorBindFusion f yz zalg =
    (interiorBind f >~> interiorFold yz zalg)
      =< interiorFoldLaw
         (f >~> interiorFold yz zalg) zalg
         (interiorBind f >~> interiorFold yz zalg)
         (\ i p -> refl (interiorFold yz zalg i (f i p)))
         (\ i c ps -> refl (zalg i) =$= (refl (c 8><_) =$= (
            ((all (interiorBind f >~> interiorFold yz zalg)
              =[ F-map->~> (interiorBind f) (interiorFold yz zalg) >=
            (all (interiorBind f) >~> all (interiorFold yz zalg))
              =< refl _>~>_
                 =$= allInteriorFoldLaw f cut'
                 =$= allInteriorFoldLaw yz zalg  ]=
            allInteriorFold f (\ i -> <_>) >~> allInteriorFold yz zalg [QED])
           =$ inners c =$= refl ps))))
      ]=
    interiorFold (f >~> interiorFold yz zalg) zalg [QED]
    where open _=>_ (ALL I)

  -- You should find that a very useful piece of kit. In fact, you should
  -- not need extensionality, either.

  -- We need Interior C to be a functor.

--??--2.12-(5)----------------------------------------------------------------

  -- using interiorBind, implement the "F-map" for Interiors as a one-liner

  interior : {X Y : I -> Set} ->
             [ X -:> Y ] -> [ Interior C X -:> Interior C Y ]
  interior f = {!!}

  -- using interiorBindFusion, prove the following law for "fold after map"

  interiorFoldFusion : {P Q R : I -> Set}
    (pq : [ P -:> Q ])(qr : [ Q -:> R ])(ralg : Algebra (CUTTING C) R) ->
    (interior pq >~> interiorFold qr ralg) == interiorFold (pq >~> qr) ralg
  interiorFoldFusion pq qr ralg =
    interior pq >~> interiorFold qr ralg
      =[ {!!} >=
    interiorFold (pq >~> qr) ralg [QED]
    where open _=>_ (ALL I)

  -- and now, using interiorFoldFusion if it helps,
  -- complete the functor construction

  INTERIOR : (I ->SET) => (I ->SET)
  INTERIOR = record
    { F-Obj      = Interior C
    ; F-map      = interior
    ; F-map-id~> = {!!}
    ; F-map->~>  = {!!}
    } where open _=>_ (ALL I)

--??--------------------------------------------------------------------------

  -- Now let's build the Monad.
  -- You should find that all the laws you have to prove follow from the
  -- fusion laws you already have.

  open MONAD INTERIOR

--??--2.13-(5)----------------------------------------------------------------

  WRAP : ID ~~> INTERIOR
  WRAP = record
    { xf         = {!!}
    ; naturality = {!!}
    }

  -- use interiorBind to define the following
  FLATTEN : (INTERIOR >=> INTERIOR) ~~> INTERIOR
  FLATTEN = record
    { xf         = {!!}
    ; naturality = {!!}
    }

  INTERIOR-Monad : Monad
  INTERIOR-Monad = record
    { unit = WRAP
    ; mult = FLATTEN
    ; unitMult = {!!}
    ; multUnit = {!!}
    ; multMult = {!!}
    } where
    open _=>_ INTERIOR

--??--------------------------------------------------------------------------

open INTERIOR
open INTERIORFOLD


-- You should be able to define an algebra on vectors for NatCut, using +V

--??--2.14-(2)----------------------------------------------------------------

NatCutVecAlg : {X : Set} -> Algebra (CUTTING NatCut) (Vec X)
NatCutVecAlg n xsc = {!!}

--??--------------------------------------------------------------------------

-- Check that it puts things together suitably when you evaluate this:

test1 : Vec Char 13
test1 = interiorFold (\ _ -> id) NatCutVecAlg 13 subbookkeeper


------------------------------------------------------------------------------
-- Cutting Up Pairs
------------------------------------------------------------------------------

module CHOICE where
  open _|>_

--??--2.15-(2)----------------------------------------------------------------

  -- Show that if you can cut up I and cut up J, then you can cut up I * J.
  -- You now have two dimensions (I and J). The idea is that you choose one
  -- dimension in which to make a cut, and keep everything in the other
  -- dimension the same.

  _+C_ : {I J : Set} ->  I |> I ->  J |> J  ->  (I * J) |> (I * J)
  Cuts   (P +C Q) (i , j) = Cuts P i + Cuts Q j
  inners (P +C Q) = {!!}

--??--------------------------------------------------------------------------

open CHOICE

-- That should get us the ability to cut up *rectangules* by cutting either
-- vertically or horizontally.

NatCut2D : (Nat * Nat) |> (Nat * Nat)
NatCut2D = NatCut +C NatCut

Matrix : Set -> Nat * Nat -> Set
Matrix X (w , h) = Vec (Vec X w) h

-- If you've done it right, you should find that the following typechecks.
-- It's the interior of a rectangle, tiled with matrices of characters.

rectangle : Interior NatCut2D (Matrix Char) (15 , 6)
rectangle = < inr (4 , 2 , refl _)
            8>< < inl (7 , 8 , refl _)
                8>< tile (strVec "seventy"
                       ,- strVec "kitchen"
                       ,- strVec "program"
                       ,- strVec "mistake"
                       ,- [])
                  , tile (strVec "thousand"
                       ,- strVec "soldiers"
                       ,- strVec "probably"
                       ,- strVec "undefine"
                       ,- [])
                  , <> >
              , tile (strVec "acknowledgement"
                   ,- strVec "procrastination"
                   ,- [])
              , <> >

-- Later, we'll use rectangular interiors as the underlying data structure
-- for a window manager.

-- But for now, one last thing.

--??--2.16-(4)----------------------------------------------------------------

-- Show that if you have a vector of n Ps for every element of a list,
-- then you can make a vector of n (All P)s .
-- Hint: Ex1 provides some useful equipment for this job.

vecAll : {I : Set}{P : I -> Set}{is : List I}{n : Nat} ->
         All (\ i -> Vec (P i) n) is -> Vec (All P is) n
vecAll {is = is} pss = {!!}

-- Given vecAll, show that algebra for any cutting can be lifted
-- to an algebra on vectors.

VecLiftAlg : {I : Set}(C : I |> I){X : I -> Set}
             (alg : Algebra (CUTTING C) X){n : Nat} ->
             Algebra (CUTTING C) (\ i -> Vec (X i) n)
VecLiftAlg C alg i (c 8>< pss) = {!!}

-- Now show that you can build an algebra for matrices
-- which handles cuts in either dimension,
-- combining them either horizontally or vertically!

NatCut2DMatAlg : {X : Set} -> Algebra (CUTTING NatCut2D) (Matrix X)
NatCut2DMatAlg _ (inl c 8>< ms) = {!!}
NatCut2DMatAlg _ (inr c 8>< ms) = {!!}

--??--------------------------------------------------------------------------

-- And that should give you a way to glue pictures together from interiors.

picture : [ Interior NatCut2D (Matrix Char) -:> Matrix Char ]
picture = interiorFold (\ _ -> id) NatCut2DMatAlg

-- You should be able to check that the following gives you something
-- sensible:

test2 = picture _ rectangle

