{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise
{-# OPTIONS --allow-unsolved-metas #-}  -- allows import, unfinished

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 2  CATEGORIES AND MONADS (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- NOTE (19/10/17)  This file is currently incomplete: more will arrive on
-- GitHub.


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

--??--2.1---------------------------------------------------------------------

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


--??--2.2---------------------------------------------------------------------

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

--??--2.3---------------------------------------------------------------------

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

--??--2.4---------------------------------------------------------------------

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

--??--2.5---------------------------------------------------------------------

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

--??--2.6---------------------------------------------------------------------

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

--??--2.6---------------------------------------------------------------------

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

open LIST-MONAD

--??--------------------------------------------------------------------------

-- More monads to come...
