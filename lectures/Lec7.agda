module Lec7 where

open import Lec1Done

data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X

foldrL : {X T : Set} -> (X -> T -> T) -> T -> List X -> T
foldrL c n [] = n
foldrL c n (x ,- xs) = c x (foldrL c n xs)

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 3 _-,_

data _<=_ {X : Set} : (xz yz : Bwd X) -> Set where
  oz : [] <= []
  os : {xz yz : Bwd X}{y : X} -> xz <= yz -> (xz -, y) <= (yz -, y)
  o' : {xz yz : Bwd X}{y : X} -> xz <= yz ->  xz       <= (yz -, y)

oe : {X : Set}{xz : Bwd X} -> [] <= xz
oe {_} {[]}      = oz
oe {_} {xz -, _} = o' oe

oi : {X : Set}{xz : Bwd X} -> xz <= xz
oi {_} {[]}      = oz
oi {_} {xz -, _} = os oi       -- look here...

_<o<_ : {X : Set}{xz yz zz : Bwd X} -> xz <= yz -> yz <= zz -> xz <= zz
th <o< o' ph = o' (th <o< ph)
oz <o< oz = oz
os th <o< os ph = os (th <o< ph)   -- ...and here
o' th <o< os ph = o' (th <o< ph)

Elem : {X : Set} -> X -> Bwd X -> Set
Elem x yz = ([] -, x) <= yz

data Ty : Set where
  one  : Ty
  list : Ty -> Ty
  _=>_ : Ty -> Ty -> Ty
infixr 4 _=>_

Val : Ty -> Set
Val one      = One
Val (list T) = List (Val T)
Val (S => T) = Val S -> Val T

data Tm (Tz : Bwd Ty) : Ty -> Set where

  var : {T : Ty} -> Elem T Tz -> Tm Tz T
  
  <> : Tm Tz one

  []   : {T : Ty} -> Tm Tz (list T)
  _,-_ : {T : Ty} -> Tm Tz T -> Tm Tz (list T) -> Tm Tz (list T)
  foldr : {S T : Ty} ->
          Tm Tz (S => T => T) ->
          Tm Tz T ->
          Tm Tz (list S)
          -> Tm Tz T

  lam : {S T : Ty} ->
        Tm (Tz -, S) T
        -> Tm Tz (S => T)
  _$$_ : {S T : Ty} ->
         Tm Tz (S => T) ->
         Tm Tz S
         -> Tm Tz T

infixl 3 _$$_

All : {X : Set} -> (X -> Set) -> Bwd X -> Set
All P []        = One
All P (xz -, x) = All P xz * P x

all : {X : Set}{P Q : X -> Set}(f : (x : X) -> P x -> Q x) -> (xz : Bwd X) -> All P xz -> All Q xz
all f [] <> = <>
all f (xz -, x) (pz , p) = all f xz pz , f x p

Env : Bwd Ty -> Set
Env = All Val

select : {X : Set}{P : X -> Set}{Sz Tz : Bwd X} -> Sz <= Tz -> All P Tz -> All P Sz
select oz     <>       = <>
select (os x) (vz , v) = select x vz , v
select (o' x) (vz , v) = select x vz

eval : {Tz : Bwd Ty}{T : Ty} -> Env Tz -> Tm Tz T -> Val T
eval vz (var x) with select x vz
eval vz (var x) | <> , v = v
eval vz <> = <>
eval vz []               = []
eval vz (t ,- ts)        = eval vz t ,- eval vz ts
eval vz (foldr c n ts)   = foldrL (eval vz c) (eval vz n) (eval vz ts)
eval vz (lam t)          = \ s -> eval (vz , s) t
eval vz (f $$ s)         = eval vz f (eval vz s)

append : {Tz : Bwd Ty}{T : Ty} ->
         Tm Tz (list T => list T => list T)
append = lam (lam (foldr (lam (lam (var (o' (os oe)) ,- var (os oe))))
           (var (os oe)) (var (o' (os oe)))))

test : Val (list one)
test = eval {[]} <> (append $$ (<> ,- []) $$ (<> ,- []))

thin : {Sz Tz : Bwd Ty} -> Sz <= Tz -> {S : Ty} -> Tm Sz S -> Tm Tz S
thin th (var x) = var (x <o< th)
thin th <> = <>
thin th [] = []
thin th (t ,- ts) = thin th t ,- thin th ts
thin th (foldr c n ts) = foldr (thin th c) (thin th n) (thin th ts) 
thin th (lam t) = lam (thin (os th) t)
thin th (f $$ s) = thin th f $$ thin th s

Subst : Bwd Ty -> Bwd Ty -> Set
Subst Sz Tz = All (Tm Tz) Sz

subst : {Sz Tz : Bwd Ty} -> Subst Sz Tz -> {S : Ty} -> Tm Sz S -> Tm Tz S
subst tz (var x) with select x tz
subst tz (var x) | <> , t = t
subst tz <> = <>
subst tz [] = []
subst tz (t ,- ts) = subst tz t ,- subst tz ts
subst tz (foldr c n ts) = foldr (subst tz c) (subst tz n) (subst tz ts)
subst tz (lam t) = lam (subst (all (\ T -> thin (o' oi)) _ tz , (var (os oe))) t)
subst tz (f $$ s) = subst tz f $$ subst tz s

record Action (M : Bwd Ty -> Bwd Ty -> Set) : Set where
  field
    varA : forall {S Sz Tz} -> M Sz Tz -> Elem S Sz -> Tm Tz S
    lamA : forall {S Sz Tz} -> M Sz Tz -> M (Sz -, S) (Tz -, S)
  act : {Sz Tz : Bwd Ty} -> M Sz Tz -> {S : Ty} -> Tm Sz S -> Tm Tz S
  act m (var x) = varA m x
  act m <> = <>
  act m [] = []
  act m (t ,- ts) = act m t ,- act m ts
  act m (foldr c n ts) = foldr (act m c) (act m n) (act m ts) 
  act m (lam t) = lam (act (lamA m) t)
  act m (f $$ s) = act m f $$ act m s

THIN : Action _<=_
Action.varA THIN th x = var (x <o< th)
Action.lamA THIN = os

SUBST : Action Subst
Action.varA SUBST tz x with select x tz
... | <> , t = t
Action.lamA SUBST tz = all (\ T -> Action.act THIN (o' oi)) _ tz , (var (os oe))

-- substitution
-- thinning
-- abstr-action

