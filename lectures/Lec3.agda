{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec3 where

open import Lec1Done
open import Lec2Done

postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
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
{-(-}
SET : Category
SET = record
        { Obj = Set
        ; _~>_ = \ S T -> S -> T
        ; id~> = id
        ; _>~>_ = _>>_
        ; law-id~>>~> = \ f -> refl f
        ; law->~>id~> = \ f -> refl f
        ; law->~>>~> = \ f g h -> refl (\ x -> h (g (f x)))
        }
{-)-}

unique->= : (m n : Nat)(p q : m >= n) -> p == q
unique->= m zero p q = refl <>
unique->= zero (suc n) () ()
unique->= (suc m) (suc n) p q = unique->= m n p q

-- A PREORDER is a category where there is at most one arrow between
-- any two objects. (So arrows are unique.)
{-(-}
NAT->= : Category
NAT->= = record
           { Obj = Nat
           ; _~>_ = _>=_
           ; id~> = \ {n} -> refl->= n
           ; _>~>_ = \ {m}{n}{p} m>=n n>=p -> trans->= m n p m>=n n>=p
           ; law-id~>>~> = \ {S} {T} f -> unique->= S T (trans->= S S T (refl->= S) f) f
           ; law->~>id~> = \ {S} {T} f -> unique->= S T (trans->= S T T f (refl->= T)) f
           ; law->~>>~> = \ {Q} {R} {S} {T} f g h ->
                              unique->= Q T _ _ {-(trans->= Q S T (trans->= Q R S f g) h)
                              (trans->= Q R T f (trans->= R S T g h)) -}
           } where
{-)-}

-- A MONOID is a category with Obj = One.
-- The values in the monoid are the *arrows*.
{-(-}
ONE-Nat : Category
ONE-Nat = record
            { Obj = One
            ; _~>_ = \ _ _ -> Nat
            ; id~> = zero
            ; _>~>_ = _+N_
            ; law-id~>>~> = zero-+N
            ; law->~>id~> = +N-zero
            ; law->~>>~> = assocLR-+N
            }
{-)-}

{-(-}
eqUnique : {X : Set}{x y : X}{p q : x == y} -> p == q
eqUnique {p = refl x} {q = refl .x} = refl (refl x)

-- A DISCRETE category is one where the only arrows are the identities.
DISCRETE : (X : Set) -> Category
DISCRETE X = record
               { Obj = X
               ; _~>_ = _==_
               ; id~> = \ {x} -> refl x
               ; _>~>_ = \ { (refl x) (refl .x) -> refl x }
               ; law-id~>>~> = \ {S} {T} f ->
                                   eqUnique
               ; law->~>id~> = \ {S} {T} f ->
                                   eqUnique
               ; law->~>>~> = \ {Q} {R} {S} {T} f g h -> eqUnique
               }
{-)-}



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

module FOO (C : Category) where
  open Category C
  X : Set
  X = Obj


postulate vmap : {n : Nat}{S T : Set} → (S → T) → Vec S n → Vec T n

{-+}
VEC : Nat -> SET => SET
VEC n = record { F-Obj = \ X -> Vec X n
               ; F-map = vmap
               ; F-map-id~> = extensionality {!!}
               ; F-map->~> = {!!}
               }
{+-}

{-(-}
VTAKE : Set -> NAT->= => SET
VTAKE X = record { F-Obj = Vec X
                 ; F-map = \ {m}{n} m>=n xs -> vTake m n m>=n xs
                 ; F-map-id~> = \ {n} -> extensionality (vTakeIdFact n)
                 ; F-map->~> = \ {m}{n}{p} m>=n n>=p ->
                     extensionality (vTakeCpFact m n p m>=n n>=p)
                 }
{-)-}

{-(-}
ADD : Nat -> NAT->= => NAT->=
ADD d = record { F-Obj = (d +N_) -- \ x -> d +N x
               ; F-map = \ {m}{n} -> help d m n
               ; F-map-id~> = \ {T} ->
                                  unique->= (d +N T) (d +N T) (help d T T (refl->= T))
                                  (refl->= (d +N T))
               ; F-map->~> = \ {R} {S} {T} f g ->
                                 unique->= (d +N R) (d +N T) (help d R T (trans->= R S T f g))
                                 (trans->= (d +N R) (d +N S) (d +N T) (help d R S f) (help d S T g))
               } where
               help : forall d m n -> m >= n -> (d +N m) >= (d +N n)
               help zero m n m>=n = m>=n
               help (suc d) m n m>=n =  help d m n m>=n 
{-)-}

{-(-}
CATEGORY : Category
CATEGORY = record
             { Obj = Category
             ; _~>_ = _=>_
             ; id~> = record
               { F-Obj = id
               ; F-map = id
               ; F-map-id~> = {!!}
               ; F-map->~> = {!!}
               }
             ; _>~>_ = \ F G -> record
               { F-Obj = F-Obj F >> F-Obj G
               ; F-map = F-map F >> F-map G
               ; F-map-id~> = {!!}
               ; F-map->~> = {!!}
               }
             ; law-id~>>~> = {!!}
             ; law->~>id~> = {!!}
             ; law->~>>~> = {!!}
             } where open _=>_
{-)-}
