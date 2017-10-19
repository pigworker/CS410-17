{-# OPTIONS --type-in-type #-}
module CS410-Categories where

open import CS410-Prelude

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

_=$'_ : {S : Set}{T : S -> Set}
       {f g : {x : S} -> T x} ->
       _==_ {forall {x : S} -> T x} f g ->
       (x : S) -> f {x} == g {x}
refl f =$' x = refl (f {x})

infixl 2 _=$'_

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

ID : {C : Category} -> C => C
ID = record
   { F-Obj = id
   ; F-map = id
   ; F-map-id~> = refl _
   ; F-map->~>  = \ f g -> refl _
   }

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

open FUNCTOR-CP public

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

open NATURAL-TRANSFORMATION public
open _~~>_ public


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
      

