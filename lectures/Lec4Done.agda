{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec4Done where

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
  ; F-map->~> = \ f g -> extensionality \ { (yes x) -> refl (yes (g (f x))) ; no -> refl no }
  }

module MAYBE-CAT where
  open Category SET
  open _=>_ MAYBE
  joinMaybe : {X : Set} -> Maybe (Maybe X) -> Maybe X
  joinMaybe no            = no        -- goes wrong sooner
  joinMaybe (yes mx)      = mx        -- maybe goes wrong later
  MAYBE-CAT : Category
  MAYBE-CAT = record
                { Obj = Set
                ; _~>_ = \ S T -> S -> Maybe T
                ; id~>  = yes
                ; _>~>_ = \ f g -> f >~> maybe g >~> joinMaybe
                ; law-id~>>~> = \ f -> extensionality \ x -> help1 (f x)
                ; law->~>id~> = \ f -> extensionality \ x -> help2 (f x)
                ; law->~>>~>  = \ f g h -> extensionality \ x -> help3 g h (f x)
                } where
    help1 : {T : Set} (w : Maybe T) -> joinMaybe (yes w) == w
    help1 mx = refl mx
    help2 : {T : Set} (w : Maybe T) -> joinMaybe (maybe yes w) == w
    help2 (yes x) = refl (yes x)
    help2 no = refl no
    help3 : {R S T : Set} (g : R -> Maybe S) (h : S -> Maybe T)
          (w : Maybe R) ->
        joinMaybe (maybe h (joinMaybe (maybe g w))) ==
        joinMaybe (maybe (\ x -> joinMaybe (maybe h (g x))) w)
    help3 g h (yes x) with g x
    help3 g h (yes x) | yes y = refl (h y)
    help3 g h (yes x) | no = refl no
    help3 g h no = refl no


module NATURAL-TRANSFORMATION {C D : Category} where
  open Category
  open _=>_

  record _~~>_ (F G : C => D) : Set where
    field
      -- one operation
      xform : {X : Obj C} -> _~>_ D (F-Obj F X) (F-Obj G X)
      -- one law
      xform-natural : {X Y : Obj C}(f : _~>_ C X Y) ->
                      _>~>_ D (F-map F f) (xform {Y})
                      ==
                      _>~>_ D (xform {X}) (F-map G f)

module MAYBE-GADGETS where
  open NATURAL-TRANSFORMATION {SET}{SET}
  open Category SET
  open _=>_ MAYBE
  open _~~>_

  unitMaybe : ID ~~> MAYBE
  unitMaybe = record
    { xform = yes
    ; xform-natural = \ f -> refl (f >~> yes)
    }

  multMaybe : (MAYBE >F> MAYBE) ~~> MAYBE
  multMaybe = record
    { xform = MAYBE-CAT.joinMaybe
    ; xform-natural = \ f -> extensionality \
       { (yes (yes x)) -> refl (yes (f x))
       ; (yes no) -> refl no
       ; no -> refl no }
    }

  law1 : {X : Set} -> (xform unitMaybe >~> xform multMaybe) == id~> {Maybe X}
  law1 = extensionality \ { (yes x) -> refl (yes x) ; no -> refl no }

  law2 : {X : Set} -> (F-map (xform unitMaybe) >~> xform multMaybe) == id~> {Maybe X}
  law2 = extensionality \ { (yes x) -> refl (yes x) ; no -> refl no }

  law3 : {X : Set} -> (xform multMaybe >~> xform multMaybe)
                   == (F-map (xform multMaybe) >~> xform multMaybe {X})
  law3 = extensionality \ { (yes (yes mx)) -> refl mx ; (yes no) -> refl no ; no -> refl no }

  MAYBE-CAT2 : Category
  MAYBE-CAT2 = record
    { Obj = Set
    ; _~>_ = \ S T -> S -> Maybe T
    ; id~> = xform unitMaybe
    ; _>~>_ = \ f g -> f >~> F-map g >~> xform multMaybe
    ; law-id~>>~> = \ f ->
        xform unitMaybe >~> F-map f >~> xform multMaybe
          =< law->~>>~> (xform unitMaybe) (F-map f) (xform multMaybe) ]=
        (xform unitMaybe >~> F-map f) >~> xform multMaybe
          =< refl (_>~> xform multMaybe) =$= xform-natural unitMaybe f ]=
        (f >~> xform unitMaybe) >~> xform multMaybe
          =[ law->~>>~> f (xform unitMaybe) (xform multMaybe) >=
        f >~> (xform unitMaybe >~> xform multMaybe)
          =[ refl (f >~>_) =$= law1 >=
        f >~> id~>
          =[ law->~>id~> f >=
        f [QED]
    ; law->~>id~> = \ f ->
        f >~> (F-map (xform unitMaybe) >~> xform multMaybe)
          =[ refl (f >~>_) =$= law2 >=
        f >~> id~>
          =[ law->~>id~> f >=
        f [QED] 
    ; law->~>>~> = \ f g h ->
        (f >~> (F-map g >~> xform multMaybe)) >~> (F-map h >~> xform multMaybe)
          =[ law->~>>~> f (F-map g >~> xform multMaybe) (F-map h >~> xform multMaybe) >=
        f >~> (F-map g >~> xform multMaybe) >~> (F-map h >~> xform multMaybe)
          =[ refl (f >~>_) =$= (
            (F-map g >~> xform multMaybe) >~> (F-map h >~> xform multMaybe)
              =[ law->~>>~> (F-map g) (xform multMaybe) (F-map h >~> xform multMaybe) >=
            F-map g >~> (xform multMaybe >~> (F-map h >~> xform multMaybe))
              =[ refl (F-map g >~>_) =$= (
                xform multMaybe >~> (F-map h >~> xform multMaybe)
                  =< law->~>>~> (xform multMaybe) (F-map h) (xform multMaybe) ]=
                (xform multMaybe >~> F-map h) >~> xform multMaybe
                  =< refl (_>~> xform multMaybe) =$= xform-natural multMaybe h ]=
                (F-map (F-map h) >~> xform multMaybe) >~> xform multMaybe
                  =[ law->~>>~> (F-map (F-map h)) (xform multMaybe) (xform multMaybe) >=
                F-map (F-map h) >~> (xform multMaybe >~> xform multMaybe)
                  =[ refl (F-map (F-map h) >~>_) =$= law3 >=
                F-map (F-map h) >~> (F-map (xform multMaybe) >~> xform multMaybe)
                  =< law->~>>~> (F-map (F-map h)) (F-map (xform multMaybe)) (xform multMaybe) ]=
                (F-map (F-map h) >~> F-map (xform multMaybe)) >~> xform multMaybe
                  =< refl (_>~> xform multMaybe) =$= F-map->~> (F-map h) (xform multMaybe) ]=
                (F-map (F-map h >~> xform multMaybe) >~> xform multMaybe) [QED]
              ) >=
            F-map g >~> (F-map (F-map h >~> xform multMaybe) >~> xform multMaybe)
              =< law->~>>~> (F-map g) (F-map (F-map h >~> xform multMaybe)) (xform multMaybe) ]=
            (F-map g >~> F-map (F-map h >~> xform multMaybe)) >~> xform multMaybe
              =< refl (_>~> xform multMaybe) =$= F-map->~> g (F-map h >~> xform multMaybe) ]=
            (F-map (g >~> F-map h >~> xform multMaybe) >~> xform multMaybe) [QED]
          ) >=
        (f >~> F-map (g >~> F-map h >~> xform multMaybe) >~> xform multMaybe) [QED]
    }

module MONAD {C : Category}(M : C => C) where
  open NATURAL-TRANSFORMATION {C}{C}
  open Category C
  open _=>_ M
  open _~~>_

  record Monad : Set where
    field
      unit :        ID ~~> M
      mult : (M >F> M) ~~> M

      unitMult : {X : Obj} -> (xform unit >~> xform mult) == id~> {F-Obj X}
      multUnit : {X : Obj} -> (F-map (xform unit) >~> xform mult) == id~> {F-Obj X}
      multMult : {X : Obj} -> (xform mult >~> xform mult) == (F-map (xform mult) >~> xform mult {X})

    KLEISLI : Category
    KLEISLI = record
      { Obj = Obj
      ; _~>_ = \ S T -> S ~> F-Obj T
      ; id~>  = xform unit
      ; _>~>_ = \ f g -> f >~> F-map g >~> xform mult
      ; law-id~>>~> = \ f ->
        xform unit >~> F-map f >~> xform mult
          =< law->~>>~> (xform unit) (F-map f) (xform mult) ]=
        (xform unit >~> F-map f) >~> xform mult
          =< refl (_>~> xform mult) =$= xform-natural unit f ]=
        (f >~> xform unit) >~> xform mult
          =[ law->~>>~> f (xform unit) (xform mult) >=
        f >~> (xform unit >~> xform mult)
          =[ refl (f >~>_) =$= unitMult >=
        f >~> id~>
          =[ law->~>id~> f >=
        f [QED]
      ; law->~>id~> = \ f ->
        f >~> (F-map (xform unit) >~> xform mult)
          =[ refl (f >~>_) =$= multUnit >=
        f >~> id~>
          =[ law->~>id~> f >=
        f [QED]
      ; law->~>>~> = \ f g h ->
        (f >~> (F-map g >~> xform mult)) >~> (F-map h >~> xform mult)
          =[ law->~>>~> f (F-map g >~> xform mult) (F-map h >~> xform mult) >=
        f >~> (F-map g >~> xform mult) >~> (F-map h >~> xform mult)
          =[ refl (f >~>_) =$= (
            (F-map g >~> xform mult) >~> (F-map h >~> xform mult)
              =[ law->~>>~> (F-map g) (xform mult) (F-map h >~> xform mult) >=
            F-map g >~> (xform mult >~> (F-map h >~> xform mult))
              =[ refl (F-map g >~>_) =$= (
                xform mult >~> (F-map h >~> xform mult)
                  =< law->~>>~> (xform mult) (F-map h) (xform mult) ]=
                (xform mult >~> F-map h) >~> xform mult
                  =< refl (_>~> xform mult) =$= xform-natural mult h ]=
                (F-map (F-map h) >~> xform mult) >~> xform mult
                  =[ law->~>>~> (F-map (F-map h)) (xform mult) (xform mult) >=
                F-map (F-map h) >~> (xform mult >~> xform mult)
                  =[ refl (F-map (F-map h) >~>_) =$= multMult >=
                F-map (F-map h) >~> (F-map (xform mult) >~> xform mult)
                  =< law->~>>~> (F-map (F-map h)) (F-map (xform mult)) (xform mult) ]=
                (F-map (F-map h) >~> F-map (xform mult)) >~> xform mult
                  =< refl (_>~> xform mult) =$= F-map->~> (F-map h) (xform mult) ]=
                (F-map (F-map h >~> xform mult) >~> xform mult) [QED]
              ) >=
            F-map g >~> (F-map (F-map h >~> xform mult) >~> xform mult)
              =< law->~>>~> (F-map g) (F-map (F-map h >~> xform mult)) (xform mult) ]=
            (F-map g >~> F-map (F-map h >~> xform mult)) >~> xform mult
              =< refl (_>~> xform mult) =$= F-map->~> g (F-map h >~> xform mult) ]=
            (F-map (g >~> F-map h >~> xform mult) >~> xform mult) [QED]
          ) >=
        (f >~> F-map (g >~> F-map h >~> xform mult) >~> xform mult) [QED]
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

bpRun : forall {X} ->  BitProcess X   -- a process to run
                   ->  List Two       -- a list of bits waiting to be input
                   ->  List Two       -- the list of bits output
                    *  Maybe          -- and, if we don't run out of input
                       (  X           -- the resulting value
                       *  List Two    -- and the unused input
                       )
bpRun (stop x)     bs                      = []         , yes (x , bs)
bpRun (send b k)   bs with bpRun k bs
bpRun (send b k)   bs | os , yes (x , is)  = (b ,- os)  , yes (x , is)
bpRun (send b k)   bs | os , no            = os         , no
bpRun (recv kt kf) []                      = []         , no
bpRun (recv kt kf) (tt ,- bs)              = bpRun kt bs
bpRun (recv kt kf) (ff ,- bs)              = bpRun kf bs

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
  helpCp : {R S T : Set} (f : R -> S)(g : S -> T) (p : BitProcess R) →
         bitProcess (f >~> g) p == (bitProcess f >~> bitProcess g) p
  helpCp f g (stop x) = refl (stop (g (f x)))
  helpCp f g (send b k) rewrite helpCp f g k = refl (send b (bitProcess g (bitProcess f k)))
  helpCp f g (recv kt kf) rewrite helpCp f g kt | helpCp f g kf
    = refl (recv (bitProcess g (bitProcess f kt)) (bitProcess g (bitProcess f kf)))
