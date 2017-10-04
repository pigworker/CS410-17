module Lec1 where

-- the -- mark introduces a "comment to end of line"


------------------------------------------------------------------------------
-- some basic "logical" types
------------------------------------------------------------------------------

data Zero : Set where
  -- to give a value in a data, choose one constructor
  -- there are no constructors
  -- so that's impossible

record One : Set where
  constructor <>
  -- to give a value in a record type, fill all its fields
  -- there are no fields
  -- so that's trivial
  --   (can we have a constructor, for convenience?)

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

_*_ : (S : Set)(T : Set) -> Set
S * T = Sg S \ _ -> T

------------------------------------------------------------------------------
-- some simple proofs
------------------------------------------------------------------------------

{-(-}
comm-* : {A : Set}{B : Set} -> A * B -> B * A
comm-* record { fst = a ; snd = b } = record { fst = b ; snd = a }
{-)-}

{-(-}
assocLR-+ : {A B C : Set} -> (A + B) + C -> A + (B + C)
assocLR-+ (inl (inl a)) = inl a
assocLR-+ (inl (inr b)) = inr (inl b)
assocLR-+ (inr c) = inr (inr c)
{-)-}

{-(-}
_$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
(f $* g) (a , b) = f a , g b
{-)-}

-- record syntax is rather ugly for small stuff; can we have constructors?

{-(-}
_$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
(f $+ g) (inl a) = inl (f a)
(f $+ g) (inr b) = inr (g b)
{-)-}

{-(-}
combinatorK : {A E : Set} -> A -> (E -> A)
combinatorK = \ a e -> a

combinatorS : {S T E : Set} -> (E -> (S -> T)) -> (E -> S) -> E -> T
combinatorS = \ est es e -> est e (es e)
{-)-}

{-(-}
id : {X : Set} -> X -> X
-- id x = x -- is the easy way; let's do it a funny way to make a point
id = (combinatorS combinatorK) (combinatorK {_} {Zero})
{-)-}

{-(-}
naughtE : {X : Set} -> Zero -> X
naughtE {X} ()
{-)-}


------------------------------------------------------------------------------
-- from logic to data
------------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat     -- recursive data type
  
{-# BUILTIN NATURAL Nat #-}
--  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

{-(-}
_+N_ : Nat -> Nat -> Nat
zero +N y = y
suc x +N y = suc (x +N y)

four : Nat
four = 2 +N 2
{-)-}


------------------------------------------------------------------------------
-- and back to logic
------------------------------------------------------------------------------

{-(-}
data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x           -- the relation that's "only reflexive"

{-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

see4 : (2 +N 2) == 4
see4 = refl 4


_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl f =$= refl x = refl (f x)
{-)-}

{-(-}
zero-+N : (n : Nat) -> (zero +N n) == n
zero-+N n = refl n

+N-zero : (n : Nat) -> (n +N zero) == n
+N-zero zero = refl zero
+N-zero (suc n) = refl suc =$= +N-zero n


assocLR-+N : (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
assocLR-+N zero y z = refl (y +N z)
assocLR-+N (suc x) y z rewrite assocLR-+N x y z = refl (suc (x +N (y +N z)))
{-)-}

------------------------------------------------------------------------------
-- computing types
------------------------------------------------------------------------------

{-(-}
_>=_ : Nat -> Nat -> Set
x     >= zero   = One
zero  >= suc y  = Zero
suc x >= suc y  = x >= y

{-
a0 : 2 >= 4
a0 = {!!}
-}

a1 : 4 >= 2
a1 = <>



refl->= : (n : Nat) -> n >= n
refl->= zero = <>
refl->= (suc n) = refl->= n

trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >= z
trans->= x y zero x>=y y>=z = <>
trans->= zero zero (suc z) x>=y ()
trans->= zero (suc y) (suc z) () y>=z
trans->= (suc x) zero (suc z) x>=y ()
trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z
{-)-}


------------------------------------------------------------------------------
-- construction by proof
------------------------------------------------------------------------------

{-(-}

difference : (m n : Nat) -> m >= n -> Sg Nat \ d -> m == (n +N d)
                                   --       (                    )
difference m zero p    = m , refl m
difference zero (suc n) ()
difference (suc m) (suc n) p with difference m n p
{-difference (suc .(n +N d)) (suc n) p
  | d , refl .(n +N d) = d , refl (suc (n +N d))
-}
difference (suc m) (suc n) p | d , q rewrite q = {!!} --  d , refl (suc (n +N d))
--difference (suc m) (suc n) p | d , q = d , (refl suc =$= q)

tryMe      = difference 42 37 _
don'tTryMe = difference 37 42 {!!}
{-)-}

------------------------------------------------------------------------------
-- things to remember to say
------------------------------------------------------------------------------

-- why the single colon?

-- what's with all the spaces?

-- what's with identifiers mixing letters and symbols?

-- what's with all the braces?

-- what is Set?

-- are there any lowercase/uppercase conventions?

-- what's with all the underscores?
--   (i)   placeholders in mixfix operators
--   (ii)  don't care (on the left)
--   (iii) go figure (on the right)

-- why use arithmetic operators for types?

-- what's the difference between = and == ?

-- can't we leave out cases?

-- can't we loop?

{-
brexit : {A : Set} -> A
brexit = brexit
-}

-- the function type is both implication and universal quantification,
-- but why is it called Pi?

-- why is Sigma called Sigma?

-- B or nor B?

{-
exMid : {B : Set} -> B + (B -> Zero)
exMid = {!!}

deMorgan : {A B : Set} -> ((A * B) -> Zero) -> (A -> Zero) + (B -> Zero)
deMorgan notAandB = {!!}
-}
