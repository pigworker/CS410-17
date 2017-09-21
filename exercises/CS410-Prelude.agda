module CS410-Prelude where


------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Standard Equipment for use in Exercises
------------------------------------------------------------------------------
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- functional equipment (types may be generalized later)
------------------------------------------------------------------------------

-- the polymorphic identity function
id : {X : Set} -> X -> X
id x = x

-- standard composition: f << g is "f after g"
_<<_ : {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> (X -> Z)
(f << g) x = f (g x)

-- diagrammatic composition: f >> g is "f then g"
_>>_ : {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
                     --       ^^^^^^^^          dominoes!
(f >> g) x = g (f x)

-- infix application
_$_ : {S : Set}{T : S -> Set}(f : (x : S) -> T x)(s : S) -> T s
f $ s = f s
infixl 2 _$_


------------------------------------------------------------------------------
-- some basic "logical" types
------------------------------------------------------------------------------

data Zero : Set where
  -- to give a value in a data, choose one constructor
  -- there are no constructors
  -- so that's impossible

record One : Set where
  -- to give a value in a record type, fill all its fields
  -- there are no fields
  -- so that's trivial
  --   (can we have a constructor, for convenience?)
  constructor <>

data _+_ (S : Set)(T : Set) : Set where -- "where" wants an indented block
  -- to offer a choice of constructors, list them with their types
  inl : S -> S + T     -- constructors can pack up stuff
  inr : T -> S + T
  -- in Haskell, this was called "Either S T"

record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
  constructor _,_
  field -- introduces a bunch of fields, listed with their types
    fst : S  
    snd : T fst
-- make _*_ from Sg ?
open Sg public

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T


------------------------------------------------------------------------------
-- natural numbers and addition
------------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat     -- recursive data type
  
{-# BUILTIN NATURAL Nat #-}
--  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc x +N y = suc (x +N y)      -- there are other choices


------------------------------------------------------------------------------
-- equality
------------------------------------------------------------------------------

data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x           -- the relation that's "only reflexive"

{-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl f =$= refl x = refl (f x)

infixl 2 _=$=_


------------------------------------------------------------------------------
-- greater-than-or-equals
------------------------------------------------------------------------------

_>=_ : Nat -> Nat -> Set
x     >= zero   = One
zero  >= suc y  = Zero
suc x >= suc y  = x >= y

refl->= : (n : Nat) -> n >= n
refl->= zero    = record {}
refl->= (suc n) = refl->= n

trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >= z
trans->=      x       y  zero    x>=y y>=z = record {}
trans->=      x  zero    (suc z) x>=y ()
trans->= zero    (suc y) (suc z) ()   y>=z
trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z

suc->= : (x : Nat) -> suc x >= x
suc->= zero    = <>
suc->= (suc x) = suc->= x
