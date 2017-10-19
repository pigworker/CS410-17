{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module Lec4 where

open import Lec1Done
open import Lec2Done
open import Lec3Done

-- the identity functor (the identity action on objects and arrows)
ID : SET => SET
ID = id~> where open Category CATEGORY

-- composition of functors (composition of actions on objects and arrows)
_>F>_ : (SET => SET) -> (SET => SET) -> (SET => SET)
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

  unMaybe : {T : Set} -> Maybe T -> T
  unMaybe (yes t) = t
  unMaybe no = {!!}

  joinMaybe : {T : Set} -> Maybe (Maybe T) -> Maybe T
  joinMaybe (yes mt) = mt
  joinMaybe no = no

  MAYBE-CAT : Category
  MAYBE-CAT = record
                { Obj = Set
                ; _~>_ = \ S T -> S -> Maybe T
                ; id~> = yes
                ; _>~>_ = \ f g -> f >~> maybe g >~> {!!}
                ; law-id~>>~> = {!!}
                ; law->~>id~> = {!!}
                ; law->~>>~> = {!!}
                }
