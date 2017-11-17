module Lec6Done where

open import Lec1Done

data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X
infixr 4 _,-_

-- ListF : Set -> Set -> Set
-- ListF X T = One + (X * T)

mkList : {X : Set} -> One + (X * List X) -> List X
mkList (inl <>)        = []
mkList (inr (x , xs))  = x ,- xs

foldr : {X T : Set} -> ((One + (X * T)) -> T) -> List X -> T
foldr alg []         = alg (inl <>)
foldr alg (x ,- xs)  = alg (inr (x , foldr alg xs))

ex1 = foldr mkList (1 ,- 2 ,- 3 ,- [])

length : {X : Set} -> List X -> Nat
length = foldr \ { (inl <>) -> zero ; (inr (x , n)) -> suc n }

record CoList (X : Set) : Set where
  coinductive
  field
    force : One + (X * CoList X)
open CoList

[]~ : {X : Set} -> CoList X
force []~ = inl <>

_,~_ : {X : Set} -> X -> CoList X -> CoList X
force (x ,~ xs) = inr (x , xs)
infixr 4 _,~_

unfoldr : {X S : Set} -> (S -> (One + (X * S))) -> S -> CoList X
force (unfoldr coalg s) with coalg s
force (unfoldr coalg s) | inl <>       = inl <>
force (unfoldr coalg s) | inr (x , s') = inr (x , unfoldr coalg s')

ex2 = unfoldr force (1 ,~ 2 ,~ 3 ,~ []~)

repeat : {X : Set} -> X -> CoList X
repeat = unfoldr \ x -> inr (x , x)

prefix : {X : Set} -> Nat -> CoList X -> List X
prefix zero xs = []
prefix (suc n) xs with force xs
prefix (suc n) xs | inl <> = []
prefix (suc n) xs | inr (x , xs') = x ,- prefix n xs'

ex2' = prefix 3 ex2

record Stream (X : Set) : Set where
  coinductive
  field
    hdTl : X * Stream X
open Stream

forever : {X : Set} -> X -> Stream X
fst (hdTl (forever x)) = x
snd (hdTl (forever x)) = forever x

unfold : {X S : Set} -> (S -> X * S) -> S -> Stream X
fst (hdTl (unfold coalg s)) = fst (coalg s)
snd (hdTl (unfold coalg s)) = unfold coalg (snd (coalg s))
