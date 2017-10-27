module Lec1Done where

-- the -- mark introduces a "comment to end of line"


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

{-# COMPILE GHC One = data () (()) #-}


data _+_ (S : Set)(T : Set) : Set where -- "where" wants an indented block
  -- to offer a choice of constructors, list them with their types
  inl : S -> S + T     -- constructors can pack up stuff
  inr : T -> S + T
  -- in Haskell, this was called "Either S T"

{-
record _*_ (S : Set)(T : Set) : Set where
  field -- introduces a bunch of fields, listed with their types
    fst : S  
    snd : T
  -- in Haskell, this was called "(S, T)"
-}

-- _*_ IS GENERALIZED BY SIGMA

record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
  constructor _,_
  field -- introduces a bunch of fields, listed with their types
    fst : S  
    snd : T fst
open Sg public -- brings fst and snd into scope hereafter unto all inheritors
-- make _*_ from Sg ?
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _*_ _,_



------------------------------------------------------------------------------
-- some simple proofs
------------------------------------------------------------------------------

comm-* : {A : Set}{B : Set} -> A * B -> B * A
comm-* record { fst = a ; snd = b } = record { fst = b ; snd = a }

assocLR-+ : {A B C : Set} -> (A + B) + C -> A + (B + C)
assocLR-+ (inl (inl a)) = inl a
assocLR-+ (inl (inr b)) = inr (inl b)
assocLR-+ (inr c)       = inr (inr c)

_$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
(f $* g) record { fst = a ; snd = b } = record { fst = f a ; snd = g b }

-- record syntax is rather ugly for small stuff; can we have constructors?

_$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
(f $+ g) (inl a) = inl (f a)
(f $+ g) (inr b) = inr (g b)

combinatorK : {A E : Set} -> A -> E -> A
combinatorK = \ a _ -> a

combinatorS : {S T E : Set} -> (E -> S -> T) -> (E -> S) -> E -> T
combinatorS = \ f s e -> (f e) (s e)

id : {X : Set} -> X -> X
-- id x = x -- is the easy way; let's do it a funny way to make a point
id = combinatorS combinatorK (combinatorK {_} {Zero})
--                          no choice for -^   ^^^^- could be anything

naughtE : {X : Set} -> Zero -> X
naughtE ()

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
-- from logic to data
------------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat     -- recursive data type
  
{-# BUILTIN NATURAL Nat #-}
--  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

_+N_ : Nat -> Nat -> Nat
zero  +N y = y
suc x +N y = suc (x +N y)      -- there are other choices

four : Nat
four = 2 +N 2


------------------------------------------------------------------------------
-- and back to logic
------------------------------------------------------------------------------

data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x           -- the relation that's "only reflexive"

{-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl f =$= refl x = refl (f x)
infixl 2 _=$=_

zero-+N : (n : Nat) -> (zero +N n) == n
zero-+N n = refl n

+N-zero : (n : Nat) -> (n +N zero) == n
+N-zero zero     = refl zero
+N-zero (suc n)  = refl suc =$= +N-zero n

assocLR-+N : (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
assocLR-+N zero    y z = refl (y +N z)
assocLR-+N (suc x) y z = refl suc =$= assocLR-+N x y z


------------------------------------------------------------------------------
-- computing types
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


------------------------------------------------------------------------------
-- construction by proof
------------------------------------------------------------------------------

{- -- MOVED UP TO REPLACE _*_
record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
  constructor _,_
  field -- introduces a bunch of fields, listed with their types
    fst : S  
    snd : T fst
-- make _*_ from Sg ?
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
-}

difference : (m n : Nat) -> m >= n -> Sg Nat \ d -> m == (n +N d)
                                   --       (                    )
difference m       zero    m>=n = m , refl m
difference zero    (suc n) ()
difference (suc m) (suc n) m>=n with difference m n m>=n
difference (suc m) (suc n) m>=n | d , q = d , (refl suc =$= q)

tryMe      = difference 42 37 _
-- don'tTryMe = difference 37 42 {!!}


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

-- the function type is both implication and universal quantification,
-- but why is it called Pi?

-- why is Sigma called Sigma?

-- B or nor B?
