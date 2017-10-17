{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec3Start where

open import Lec1Done
open import Lec2Done

postulate
  extensionality : {S : Set}{T : S -> Set}
                   (f g : (x : S) -> T x) ->
                   ((x : S) -> f x == g x) ->
                   f == g

record Category : Set where
  field

    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj -> Obj -> Set    -- "arrows" or "morphisms"
                                -- or "homomorphisms"
                
    -- two operations
    id~>        : {T : Obj} ->      T ~> T
    _>~>_       : {R S T : Obj} ->  R ~> S  ->  S ~> T  ->  R ~> T

    -- three laws
    law-id~>>~> : {S T : Obj}     (f : S ~> T) ->
                    (id~> >~> f) == f
    law->~>id~> : {S T : Obj}     (f : S ~> T) ->
                    (f >~> id~>) == f
    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) ->
                    ((f >~> g) >~> h) == (f >~> (g >~> h))

-- Sets and functions are the classic example of a category.
{-+}
SET : Category
SET = {!!}
{+-}

-- A PREORDER is a category where there is at most one arrow between
-- any two objects. (So arrows are unique.)
{-+}
NAT->= : Category
NAT->= = {!!} where
  unique : (m n : Nat)(p q : m >= n) -> p == q
  unique m n p q = {!!}
{+-}

-- A MONOID is a category with Obj = One.
-- The values in the monoid are the *arrows*.
{-+}
ONE-Nat : Category
ONE-Nat = {!!}
{+-}

{-+}
eqUnique : {X : Set}{x y : X}(p q : x == y) -> p == q
eqUnique p q = {!!}

-- A DISCRETE category is one where the only arrows are the identities.
DISCRETE : (X : Set) -> Category
DISCRETE X = {!!}
{+-}



module FUNCTOR where
  open Category
  
  record _=>_ (C D : Category) : Set where  -- "Functor from C to D"
    field
      -- two actions
      F-Obj : Obj C -> Obj D
      F-map : {S T : Obj C} -> _~>_ C S T -> _~>_ D (F-Obj S) (F-Obj T)

      -- two laws
      F-map-id~> : {T : Obj C} -> F-map (id~> C {T}) == id~> D {F-Obj T}
      F-map->~>  : {R S T : Obj C}(f : _~>_ C R S)(g : _~>_ C S T) ->
                     F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)

open FUNCTOR

{-+}
VEC : Nat -> SET => SET
VEC n = {!!}
{+-}

{-+}
VTAKE : Set -> NAT->= => SET
VTAKE X = {!!}
{+-}

{-+}
ADD : Nat -> NAT->= => NAT->=
ADD d = {!!}
{+-}

{-+}
CATEGORY : Category
CATEGORY = {!!}
{+-}
