{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec4 where

open import Lec1Done
open import Lec2Done
open import Lec3Done

-- the identity functor (the identity action on objects and arrows)
ID : {C : Category} -> C => C
ID = id~> where open Category CATEGORY

-- composition of functors (composition of actions on objects and arrows)
_>F>_ : {C D E : Category} -> (C => D) -> (D => E) -> (C => E)
F >F> G = F >~> G where open Category CATEGORY

-- EXAMPLES

data Maybe (X : Set) : Set where
  yes : (x : X) -> Maybe X
  no  : Maybe X

maybe : {X Y : Set} -> (X -> Y) -> Maybe X -> Maybe Y
maybe f (yes x) = yes (f x)
maybe f no      = no

MAYBE : SET => SET
MAYBE = record
  { F-Obj = Maybe
  ; F-map = maybe
  ; F-map-id~> = extensionality \ { (yes x) -> refl (yes x) ; no -> refl no }
  -- extensionality \ { (yes x) -> refl (yes x) ; no -> refl no }
  ; F-map->~> = \ f g -> extensionality \ { (yes x) -> refl (yes (g (f x))) ; no -> refl no }
  }

module MAYBE-CAT where
  open Category SET
  open _=>_ MAYBE

{-
  unMaybe : {T : Set} -> Maybe T -> T
  unMaybe (yes t) = t
  unMaybe no = {!!}
-}

  joinMaybe : {T : Set} -> Maybe (Maybe T) -> Maybe T
  joinMaybe (yes mt) = mt
  joinMaybe no = no

  MAYBE-CAT : Category
  MAYBE-CAT = record
                { Obj = Set
                ; _~>_ = \ S T -> S -> Maybe T
                ; id~> = yes
                ; _>~>_ = \ f g -> f >> (F-map g >> joinMaybe)
                ; law-id~>>~> = \ f -> refl f
                ; law->~>id~> = \ f -> extensionality \ x -> help f x
                ; law->~>>~> = \ f g h -> extensionality \ x -> yelp f g h x
                } where
                help : forall {S T} (f : S -> Maybe T)
                  (x : S) ->
                  joinMaybe (maybe yes (f x)) == f x
                help f x with f x
                help f x | yes y = refl (yes y)
                help f x | no = refl no
                yelp : forall {Q R S T}
                  (f : Q -> Maybe R) (g : R -> Maybe S)(h : S -> Maybe T)
                  (x : Q) ->
                  joinMaybe (maybe h (joinMaybe (maybe g (f x)))) ==
                  joinMaybe
                    (maybe (\ y → joinMaybe (maybe h (g y))) (f x))
                yelp f g h x with f x
                yelp f g h x | yes y = refl (joinMaybe (maybe h (g y)))
                yelp f g h x | no = refl no

open MAYBE-CAT

module NATURAL-TRANSFORMATION {C D : Category} where
  open Category
  open _=>_

  record _~~>_ (F G : C => D) : Set where
    field
      -- one operation
      xf : {X : Obj C} -> _~>_ D (F-Obj F X) (F-Obj G X)
      -- one law
      naturality : {X Y : Obj C}(f : _~>_ C X Y) ->
                   _>~>_ D (F-map F f) (xf {Y})
                   ==
                   _>~>_ D (xf {X}) (F-map G f)

module FUNCTOR-CP {C D E : Category} where
  open _=>_
  open Category
  
  _>=>_ : C => D  ->  D => E  ->  C => E

  F-Obj (F >=> G) = F-Obj F >> F-Obj G

  F-map (F >=> G) = F-map F >> F-map G

  F-map-id~> (F >=> G) =
    F-map G (F-map F (id~> C))
      =[ refl (F-map G) =$= F-map-id~> F >=
    F-map G (id~> D)
      =[ F-map-id~> G >=
    id~> E
      [QED]

  F-map->~> (F >=> G) f g =
    F-map G (F-map F (_>~>_ C f g))
      =[ refl (F-map G) =$= F-map->~> F f g >=
    F-map G (_>~>_ D (F-map F f) (F-map F g))
      =[ F-map->~> G (F-map F f) (F-map F g) >=
    _>~>_ E (F-map G (F-map F f)) (F-map G (F-map F g))
      [QED]

open FUNCTOR-CP 

open NATURAL-TRANSFORMATION public
open _~~>_ public

UNIT-MAYBE : ID ~~> MAYBE
xf UNIT-MAYBE = yes
naturality UNIT-MAYBE f = refl _

MULT-MAYBE : (MAYBE >=> MAYBE) ~~> MAYBE
MULT-MAYBE = record { xf = joinMaybe
  ; naturality = \ f -> extensionality \ {
       (yes x) → refl (maybe f x)
      ; no → refl no } }


module MONAD {C : Category}(M : C => C) where
  open Category C
  open _=>_ M

  record Monad : Set where
    field
      unit :        ID ~~> M
      mult : (M >=> M) ~~> M

      unitMult : {X : Obj} -> (xf unit >~> xf mult) == id~> {F-Obj X}
      multUnit : {X : Obj} -> (F-map (xf unit) >~> xf mult) == id~> {F-Obj X}
      multMult : {X : Obj} -> (xf mult >~> xf mult) == (F-map (xf mult) >~> xf mult {X})

    KLEISLI : Category
    KLEISLI = record
      { Obj = Obj
      ; _~>_ = \ S T -> S ~> F-Obj T
      
      ; id~>  = xf unit
      ; _>~>_ = \ f g -> f >~> F-map g >~> xf mult
      
      ; law-id~>>~> = \ f ->
        xf unit >~> F-map f >~> xf mult
          =< law->~>>~> _ _ _ ]=
        (xf unit >~> F-map f) >~> xf mult
          =< refl (_>~> xf mult) =$= naturality unit f ]=
        (f >~> xf unit) >~> xf mult
          =[ law->~>>~> _ _ _ >=
        f >~> (xf unit >~> xf mult)
        
          =[ refl (f >~>_) =$= unitMult >=
          
        f >~> id~>
          =[ law->~>id~> f >=
        f [QED]
        
      ; law->~>id~> = \ f ->
        f >~> (F-map (xf unit) >~> xf mult)

          =[ refl (f >~>_) =$= multUnit >=

        f >~> id~>
          =[ law->~>id~> f >=
        f [QED]

      ; law->~>>~> = \ f g h ->
        (f >~> F-map g >~> xf mult) >~> F-map h >~> xf mult
          =[ law->~>>~> _ _ _ >=
        f >~> (F-map g >~> xf mult) >~> (F-map h >~> xf mult)
          =[ refl (\ x -> _ >~> x) =$= law->~>>~> _ _ _ >=
        f >~> F-map g >~> xf mult >~> F-map h >~> xf mult
          =< refl (\ x -> _ >~> _ >~> x) =$= assocn (naturality mult _) ]=
        f >~> F-map g >~> F-map (F-map h) >~> xf mult >~> xf mult
        
          =[ refl (\ x -> _ >~> _ >~> _ >~> x) =$= multMult >=

        f >~> F-map g >~> F-map (F-map h) >~> F-map (xf mult) >~> xf mult
          =< refl (\ x -> _ >~> _ >~> x) =$= law->~>>~> _ _ _ ]=
        f >~> F-map g >~> (F-map (F-map h) >~> F-map (xf mult)) >~> xf mult
          =< refl (\ x -> _ >~> _ >~> x >~> _) =$= F-map->~> _ _ ]=
        f >~> F-map g >~> F-map (F-map h >~> xf mult) >~> xf mult
          =< refl (\ x -> _ >~> x) =$= law->~>>~> _ _ _ ]=
        f >~> (F-map g >~> F-map (F-map h >~> xf mult)) >~> xf mult
          =< refl (\ x -> _ >~> x >~> _) =$= F-map->~> _ _ ]=
        f >~> F-map (g >~> F-map h >~> xf mult) >~> xf mult
          [QED]
      }

open MONAD public

MAYBE-Monad : Monad MAYBE
MAYBE-Monad = record
  { unit = UNIT-MAYBE
  ; mult = MULT-MAYBE
  ; unitMult = refl id
  ; multUnit = extensionality \
     { (yes x) -> refl (yes x) ; no -> refl no }
  ; multMult = extensionality \
     { (yes x) -> refl (joinMaybe x) ; no -> refl no }
  }

data List (X : Set) : Set where
  []   : List X
  _,-_ : (x : X)(xs : List X) -> List X

list : {X Y : Set} -> (X -> Y) -> List X -> List Y
list f []         = []
list f (x ,- xs)  = f x ,- list f xs

LIST : SET => SET
LIST = record
  { F-Obj = List
  ; F-map = list
  ; F-map-id~> = extensionality listId
  ; F-map->~> = \ f g -> extensionality (listCp f g)
  } where
  open Category SET
  listId : {T : Set}(xs : List T) -> list id xs == xs
  listId []        = refl []
  listId (x ,- xs) = refl (_,-_ x) =$= listId xs
  listCp : {R S T : Set} (f : R -> S) (g : S -> T) (xs : List R) →
           list (f >~> g) xs == (list f >~> list g) xs
  listCp f g [] = refl []
  listCp f g (x ,- xs) = refl (_,-_ (g (f x))) =$= listCp f g xs

data Two : Set where tt ff : Two

data BitProcess (X : Set) : Set where  -- in what way is X used?
  stop : (x : X) -> BitProcess X                       -- stop with value x
  send : (b : Two)(k : BitProcess X) -> BitProcess X   -- send b, continue as k
  recv : (kt kf : BitProcess X) -> BitProcess X        -- receive bit, continue as
                                                       --   kt if tt, kf if ff

{-+}
send1 : (b : Two) -> BitProcess One
send1 b = ?
{+-}

{-+}
recv1 : BitProcess Two
recv1 = ?
{+-}

{-+}
bpRun : forall {X} ->  BitProcess X   -- a process to run
                   ->  List Two       -- a list of bits waiting to be input
                   ->  List Two       -- the list of bits output
                    *  Maybe          -- and, if we don't run out of input
                       (  X           -- the resulting value
                       *  List Two    -- and the unused input
                       )
bpRun px bs = {!!}
{+-}

bitProcess : {X Y : Set} -> (X -> Y) -> BitProcess X -> BitProcess Y
bitProcess f (stop x) = stop (f x)
bitProcess f (send b k) = send b (bitProcess f k)
bitProcess f (recv kt kf) = recv (bitProcess f kt) (bitProcess f kf)

BITPROCESS : SET => SET  -- actions on *values* lift to processes
BITPROCESS = record
  { F-Obj = BitProcess
  ; F-map = bitProcess
  ; F-map-id~> = extensionality helpId
  ; F-map->~> = \ f g -> extensionality (helpCp f g)
  } where
  open Category SET
  helpId : {T : Set} (p : BitProcess T) -> bitProcess id p == p
  helpId (stop x) = refl (stop x)
  helpId (send b k) rewrite helpId k = refl (send b k)
  helpId (recv kt kf) rewrite helpId kt | helpId kf = refl (recv kt kf)
  helpCp : {R S T : Set} (f : R -> S)(g : S -> T) (p : BitProcess R) ->
         bitProcess (f >~> g) p == (bitProcess f >~> bitProcess g) p
  helpCp f g (stop x) = refl (stop (g (f x)))
  helpCp f g (send b k) rewrite helpCp f g k = refl (send b (bitProcess g (bitProcess f k)))
  helpCp f g (recv kt kf) rewrite helpCp f g kt | helpCp f g kf
    = refl (recv (bitProcess g (bitProcess f kt)) (bitProcess g (bitProcess f kf)))

{-+}
UNIT-BP : ID ~~> BITPROCESS
UNIT-BP = {!!}
{+-}

{-+}
MULT-BP : (BITPROCESS >=> BITPROCESS) ~~> BITPROCESS
MULT-BP = {!!}
{+-}

{-+}
BITPROCESS-Monad : Monad BITPROCESS
BITPROCESS-Monad = record
  { unit = UNIT-BP
  ; mult = MULT-BP
  ; unitMult = {!!}
  ; multUnit = {!!}
  ; multMult = {!!}
  } where
{+-}

module BIND {F : SET => SET}(M : Monad F) where

  open _=>_ F public
  open Monad M public
  open Category KLEISLI public

  {-+}
  _>>=_ : {S T : Set} -> F-Obj S -> (S -> F-Obj T) -> F-Obj T
  fs >>= k = {!!}
  {+-}
