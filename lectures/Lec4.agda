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
{-# COMPILE GHC Maybe = data Maybe (Just | Nothing) #-}

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
  ; unitMult = refl _
  ; multUnit = extensionality \ { (yes x) -> refl _ ; no -> refl _ }
  ; multMult = extensionality \ { (yes mmx) -> refl _ ; no -> refl _ }
  }

data List (X : Set) : Set where
  []   : List X
  _,-_ : (x : X)(xs : List X) -> List X
{-# COMPILE GHC List = data [] ([] | (:)) #-}

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
{- BUILTIN BOOL Two -}
{- BUILTIN FALSE ff -}
{- BUILTIN TRUE tt -}
{-# COMPILE GHC Two = data Bool (True | False) #-}

data BitProcess (X : Set) : Set where  -- in what way is X used?
  stop : (x : X) -> BitProcess X                       -- stop with value x
  send : (b : Two)(k : BitProcess X) -> BitProcess X   -- send b, continue as k
  recv : (kt kf : BitProcess X) -> BitProcess X        -- receive bit, continue as
                                                       --   kt if tt, kf if ff

{-(-}
send1 : (b : Two) -> BitProcess One
send1 b = send b (stop <>)
{-)-}

{-(-}
recv1 : BitProcess Two
recv1 = recv (stop tt) (stop ff)
{-)-}

{-(-}
bpRun : forall {X} ->  BitProcess X   -- a process to run
                   ->  List Two       -- a list of bits waiting to be input
                   ->  List Two       -- the list of bits output
                    *  Maybe          -- and, if we don't run out of input
                       (  X           -- the resulting value
                       *  List Two    -- and the unused input
                       )
bpRun (stop x) bs = [] , yes (x , bs)
bpRun (send b px) bs = let os , mz = bpRun px bs in (b ,- os) , mz
bpRun (recv pxt pxf) [] = [] , no
bpRun (recv pxt pxf) (tt ,- bs) = bpRun pxt bs
bpRun (recv pxt pxf) (ff ,- bs) = bpRun pxf bs
{-)-}

example = bpRun recv1 (tt ,- [])

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

{-(-}
UNIT-BP : ID ~~> BITPROCESS
UNIT-BP = record { xf = stop
                 ; naturality = \ f -> refl _
                 }
{-)-}

join-BP : {X : Set} -> BitProcess (BitProcess X) -> BitProcess X
join-BP (stop px) = px
join-BP (send b ppx) = send b (join-BP ppx)
join-BP (recv ppxt ppxf) = recv (join-BP ppxt) (join-BP ppxf)

{-(-}
MULT-BP : (BITPROCESS >=> BITPROCESS) ~~> BITPROCESS
MULT-BP = record
  { xf = join-BP
  ; naturality = \ f -> extensionality (help f )
  } where
  help : ∀ {X Y} (f : X → Y) (x : BitProcess (BitProcess X)) →
       join-BP (bitProcess (bitProcess f) x) == bitProcess f (join-BP x)
  help f (stop x) = refl (bitProcess f x)
  help f (send b p) rewrite help f p
    = refl (send b (bitProcess f (join-BP p)))
  help f (recv pt pf) rewrite help f pf | help f pt
    = refl (recv (bitProcess f (join-BP pt)) (bitProcess f (join-BP pf)))
{-)-}

{-(-}
BITPROCESS-Monad : Monad BITPROCESS
BITPROCESS-Monad = record
  { unit = UNIT-BP
  ; mult = MULT-BP
  ; unitMult = refl id
  ; multUnit = extensionality help
  ; multMult = extensionality yelp
  } where
  
  help : ∀ {X} (x : BitProcess X) → join-BP (bitProcess stop x) == x
  help (stop x) = refl (stop x)
  help (send b p)  rewrite help p = refl (send b p)
  help (recv pt pf) rewrite help pt | help pf = refl (recv pt pf)
  
  yelp : ∀ {X} (x : BitProcess (BitProcess (BitProcess X))) →
       join-BP (join-BP x) == join-BP (bitProcess join-BP x)
  yelp (stop x) = refl _
  yelp (send b p)  rewrite yelp p = refl _
  yelp (recv pt pf) rewrite yelp pt | yelp pf = refl _
       
{-)-}

module BIND {F : SET => SET}(M : Monad F) where

  open _=>_ F public
  open Monad M public
  open Category KLEISLI public

  {-(-}
  _>>=_ : {S T : Set} -> F-Obj S -> (S -> F-Obj T) -> F-Obj T
  fs >>= k = (id >~> k) fs
  {-)-}

open BIND BITPROCESS-Monad

bpEcho : BitProcess One
bpEcho = recv1 >>= \ b ->
         send1 b

BP-SEM : Set -> Set
BP-SEM X = List Two       -- a list of bits waiting to be input
           ->  List Two       -- the list of bits output
           *  Maybe          -- and, if we don't run out of input
           (  X           -- the resulting value
           *  List Two    -- and the unused input
           )

record _**_ (S T : Set) : Set where
  constructor _,_
  field
    outl : S
    outr : T
open _**_
{-# COMPILE GHC _**_ = data (,) ((,)) #-}
infixr 4 _**_ _,_

postulate       -- Haskell has a monad for doing IO, which we use at the top level
  IO        : Set -> Set
  mainLoop  : {S : Set} -> S -> (S -> Two -> (List Two ** Maybe S)) -> IO One
  mainOutIn : {S : Set} -> S -> (S -> (List Two ** Maybe (Two -> S))) -> IO One

{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC mainLoop = (\ _ -> Lec4HS.mainLoop) #-}
{-# COMPILE GHC mainOutIn = (\ _ -> Lec4HS.mainOutIn) #-}
{-# FOREIGN GHC import qualified Lec4HS #-}

STATE : Set
STATE = Two -> BitProcess One

step : STATE -> Two -> (List Two ** Maybe STATE)
step s b = go (s b)
  where
    go : BitProcess One → List Two ** Maybe (Two → BitProcess One)
    go (stop <>) = [] , no
    go (send b p) with go p
    ...              | bs , ms = (b ,- bs) , ms
    go (recv pt pf) = [] , yes \ { tt → pt ; ff → pf }

myState : STATE
myState tt = bpEcho >>= \ _ -> bpEcho
myState ff = bpEcho

{-
main : IO One
main = mainLoop myState step
-}

example2 = bpRun (myState ff) (tt ,- ff ,- [])

outIn : BitProcess One -> List Two ** Maybe (Two -> BitProcess One)
outIn (stop <>) = [] , no
outIn (send b p) with outIn p
... | os , mk = (b ,- os) , mk
outIn (recv pt pf) = [] , yes \ { tt → pt ; ff → pf }

main : IO One
main = mainOutIn (send1 ff >>= \ _ -> bpEcho >>= \ _ -> bpEcho) outIn



_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i    -- [_] {I} P = (i : I) -> P i

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

All : {X : Set} -> (X -> Set) -> (List X -> Set)
All P [] = One
All P (x ,- xs) = P x * All P xs

example3 : All (Vec Two) (1 ,- 2 ,- 3 ,- [])
example3 = (tt ,- [])
         , (tt ,- ff ,- [])
         , (tt ,- ff ,- tt ,- [])
         , <>

record _|>_ (I O : Set) : Set where
  field
    Cuts   : O -> Set                      -- given o : O, how may we cut it?
    inners : {o : O} -> Cuts o -> List I   -- given how we cut it, what are
                                           --   the shapes of its pieces?

-- Let us have some examples right away!

copy : Nat -> List One
copy zero = []
copy (suc n) = <> ,- copy n

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

example4 : Cutting NatCut (Vec Two) 5
example4 = (3 , 2 , refl 5) 8>< ((tt ,- tt ,- tt ,- []) , (ff ,- ff ,- []) , <>)

data Interior {I}(C : I |> I)(T : I -> Set)(i : I) : Set where
                                         -- either...
  tile : T i -> Interior C T i           -- we have a tile that fits, or...
  <_>  : Cutting C (Interior C T) i ->   -- ...we cut, then tile the pieces.
         Interior C T i

MayC : One |> One
MayC = record { Cuts = \ _ -> One ; inners = \ _ -> [] }

Maybe' : Set -> Set
Maybe' X = Interior MayC (\ _ -> X) <>

yes' : {X : Set} -> X -> Maybe' X
yes' x = tile x

no' : {X : Set} -> Maybe' X
no' = < <> 8>< <> >

BPC : One |> One
BPC = record { Cuts = \ _ -> Two + One
             ; inners = \ { (inl x) → <> ,- []
                          ; (inr x) → <> ,- <> ,- []
                          }
             }

data Type : Set where nat two : Type

Val : Type -> Set
Val nat = Nat
Val two = Two

data Op : Type -> Set where
  val : {T : Type} -> Val T -> Op T
  add : Op nat
  if : {T : Type} -> Op T

Syntax : Type |> Type
_|>_.Cuts Syntax T = Op T
_|>_.inners Syntax {T} (val x) = []
_|>_.inners Syntax {.nat} add = nat ,- nat ,- []
_|>_.inners Syntax {T} if = two ,- T ,- T ,- []

eval : {T : Type}{X : Type -> Set} -> Interior Syntax X T ->
       ({T : Type} -> X T -> Val T) -> Val T
eval (tile x) g = g x
eval < val v 8>< <> > g = v
eval < add 8>< e1 , e2 , <> > g = eval e1 g +N eval e2 g
eval < if 8>< e1 , e2 , e3 , <> > g with eval e1 g
eval < if 8>< e1 , e2 , e3 , <> > g | tt = eval e2 g
eval < if 8>< e1 , e2 , e3 , <> > g | ff = eval e3 g
