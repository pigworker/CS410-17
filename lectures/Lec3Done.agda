{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec3Done where

open import Lec1Done
open import Lec2Done

postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g

imp : {S : Set}{T : S -> Set}(f : (x : S) -> T x){x : S} -> T x
imp f {x} = f x

extensionality' : {S : Set}{T : S -> Set}
                   {f g : {x : S} -> T x} ->
                   ((x : S) -> f {x} == g {x}) ->
                   _==_ {forall {x : S} -> T x} f g
extensionality' {f = f}{g = g} q =
  refl imp =$= extensionality {f = \ x -> f {x}}{g = \ x -> g {x}}
    q                    

_[QED] : {X : Set}(x : X) -> x == x
x [QED] = refl x
_=[_>=_ : {X : Set}(x : X){y z : X} -> x == y -> y == z -> x == z
x =[ refl .x >= q = q
_=<_]=_ : {X : Set}(x : X){y z : X} -> y == x -> y == z -> x == z
x =< refl .x ]= q = q
infixr 1 _=[_>=_ _=<_]=_
infixr 2 _[QED]

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

  assocn : {Q R R' S T : Obj}
            {f  : Q ~> R} {g : R ~> S}
            {f' : Q ~> R'}{g' : R' ~> S}
            {h : S ~> T} ->
            (f >~> g) == (f' >~> g') ->
            (f >~> g >~> h) == (f' >~> g' >~> h)
  assocn {f = f} {g = g} {f' = f'} {g' = g'} {h = h} q =
    f >~> g >~> h
      =< law->~>>~> _ _ _ ]=
    (f >~> g) >~> h
      =[ refl _>~>_ =$= q =$= refl h >=
    (f' >~> g') >~> h
      =[ law->~>>~> _ _ _ >=
    f' >~> g' >~> h
      [QED]

  infixr 3 _>~>_

-- Sets and functions are the classic example of a category.
SET : Category
SET = record
        { Obj         = Set
        ; _~>_        = \ S T -> S -> T
        ; id~>        = id
        ; _>~>_       = _>>_
        ; law-id~>>~> = \ f -> refl f
        ; law->~>id~> = \ f -> refl f
        ; law->~>>~>  = \ f g h -> refl (f >> (g >> h))
        }

-- A PREORDER is a category where there is at most one arrow between
-- any two objects. (So arrows are unique.)
NAT->= : Category
unique->= : (m n : Nat)(p q : m >= n) -> p == q
unique->= m zero p q = refl <>
unique->= zero (suc n) () q
unique->= (suc m) (suc n) p q = unique->= m n p q

NAT->= = record
           { Obj         = Nat
           ; _~>_        = _>=_
           ; id~>        = \ {n} -> refl->= n
           ; _>~>_       = \ {m}{n}{p} m>=n n>=p -> trans->= m n p m>=n n>=p
           ; law-id~>>~> = \ {m}{n} m>=n -> unique->= m n _ _
           ; law->~>id~> = \ {m}{n} m>=n -> unique->= m n _ _
           ; law->~>>~>  = \ {m}{n}{p}{q} m>n n>=p p>=q -> unique->= m q _ _
           } where

-- A MONOID is a category with Obj = One.
-- The values in the monoid are the *arrows*.
ONE-Nat : Category
ONE-Nat = record
            { Obj         = One
            ; _~>_        = \ _ _ -> Nat
            ; id~>        = 0
            ; _>~>_       = _+N_
            ; law-id~>>~> = \ n -> zero-+N n
            ; law->~>id~> = \ n -> +N-zero n
            ; law->~>>~>  = \ m n p -> assocLR-+N m n p
            }

eqUnique : {X : Set}{x y : X}(p q : x == y) -> p == q
eqUnique (refl x) (refl .x) = refl (refl x)

-- A DISCRETE category is one where the only arrows are the identities.
DISCRETE : (X : Set) -> Category
DISCRETE X = record
               { Obj         = X
               ; _~>_        = _==_
               ; id~>        = refl _
               ; _>~>_       = \ { {x} (refl .x) (refl .x) -> refl x }
               ; law-id~>>~> = \ _ -> eqUnique _ _
               ; law->~>id~> = \ _ -> eqUnique _ _
               ; law->~>>~>  = \ _ _ _ -> eqUnique _ _
               }

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

open FUNCTOR public

postulate homework : {A : Set} -> A

VEC : Nat -> SET => SET
VEC n = record
  { F-Obj       = \ X -> Vec X n
  ; F-map       = homework
  ; F-map-id~>  = homework
  ; F-map->~>   = homework
  }

VTAKE : Set -> NAT->= => SET
VTAKE X = record
  { F-Obj      = Vec X
  ; F-map      = \ {m}{n} m>=n xs -> vTake m n m>=n xs
  ; F-map-id~> = \ {n} -> extensionality \ xs -> vTakeIdFact n xs
  ; F-map->~>  = \ {m}{n}{p} m>=n n>=p -> extensionality \ xs ->
     vTakeCpFact m n p m>=n n>=p xs
  }

ADD : Nat -> NAT->= => NAT->=
ADD d = record { F-Obj = (d +N_)
               ; F-map = \ {m}{n} -> help d m n
               ; F-map-id~> = \ {n} -> unique->= (d +N n) (d +N n) _ _
               ; F-map->~> = \ {m}{n}{p} x y ->
                  unique->= (d +N m) (d +N p) _ _
               } where
  help : (d m n : Nat) -> m >= n -> (d +N m) >= (d +N n)
  help zero m n m>=n = m>=n
  help (suc d) m n m>=n = help d m n m>=n

Thing : {C D : Category}(F G : C => D) -> Set
Thing {C}{D}
      (record { F-Obj = F-Obj ; F-map = F-map
              ; F-map-id~> = F-map-id~> ; F-map->~> = F-map->~> })
      (record { F-Obj = G-Obj ; F-map = G-map
              ; F-map-id~> = G-map-id~> ; F-map->~> = G-map->~> })
  = Sg (F-Obj == G-Obj)
     \ { (refl _) ->
    Sg (_==_ {forall {S T : Category.Obj C} →
          (C Category.~> S) T → (D Category.~> F-Obj S) (F-Obj T)}
          F-map  G-map)
     \ { (refl _) ->
       _==_ {forall {T : Category.Obj C} →
      F-map (Category.id~> C {T}) == Category.id~> D} F-map-id~> G-map-id~>
       *
       _==_ {forall {R S T : Category.Obj C} (f : (C Category.~> R) S)
      (g : (C Category.~> S) T) →
      F-map ((C Category.>~> f) g) == (D Category.>~> F-map f) (F-map g)}
        F-map->~>  G-map->~>
     }}

Lemma : {C D : Category}{F G : C => D} -> Thing F G -> F == G
Lemma (refl _ , (refl _ , (refl _ , refl _))) = refl _


CATEGORY : Category
CATEGORY = record
             { Obj = Category
             ; _~>_ = _=>_
             ; id~> = record { F-Obj = \ X -> X
                             ; F-map = \ a -> a
                             ; F-map-id~> = refl _
                             ; F-map->~> = \ _ _ -> refl _ }
             ; _>~>_ = \ {R}{S}{T} F G -> record
               { F-Obj = F-Obj F >> F-Obj G
               ; F-map = F-map F >> F-map G
               ; F-map-id~> = F-map G (F-map F (Category.id~> R))
                                =[ refl (F-map G) =$= F-map-id~> F >=
                              F-map G (Category.id~> S)
                                =[ F-map-id~> G >=
                              Category.id~> T
                                [QED]
               ; F-map->~> = \ f g ->
                   F-map G (F-map F (Category._>~>_ R f g))
                     =[ refl (F-map G) =$= F-map->~> F f g >=
                   F-map G (Category._>~>_ S (F-map F f) (F-map F g))
                     =[ F-map->~> G (F-map F f) (F-map F g) >=
                   Category._>~>_ T (F-map G (F-map F f))
                                    (F-map G (F-map F g))
                     [QED]
               }
             ; law-id~>>~> = \ F -> Lemma
                 ((refl _) , ((refl _) ,
                    (extensionality' (\ x -> eqUnique _ _) ,
                    extensionality' (\ x ->
                      extensionality' \ y -> extensionality' \ z ->
                        extensionality \ f -> extensionality \ g ->
                          eqUnique _ _))))
             ; law->~>id~> = \ F -> Lemma
                 ((refl _) , ((refl _) ,
                    (extensionality' (\ x -> eqUnique _ _) ,
                    extensionality' (\ x ->
                      extensionality' \ y -> extensionality' \ z ->
                        extensionality \ f -> extensionality \ g ->
                          eqUnique _ _))))
             ; law->~>>~> = \ F G H ->  Lemma
                 ((refl _) , ((refl _) ,
                    (extensionality' (\ x -> eqUnique _ _) ,
                    extensionality' (\ x ->
                      extensionality' \ y -> extensionality' \ z ->
                        extensionality \ f -> extensionality \ g ->
                          eqUnique _ _))))
             } where
             open _=>_
            
