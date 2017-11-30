{-# OPTIONS --type-in-type #-}

module Lec6 where

open import Lec1Done

ListF : Set -> Set -> Set
ListF X T = One + (X * T)

data List (X : Set) : Set where
  <_> : (ListF X) (List X) -> (List X)
infixr 4 _,-_

listF : {X T U : Set} -> (T -> U) -> (ListF X) T -> (ListF X) U
listF g (inl <>)      = inl <>
listF g (inr (x , t)) = inr (x , g t)

pattern []        = < inl <> >
pattern _,-_ x xs = < inr (x , xs) >

{-(-}
mkList : {X : Set} -> (ListF X) (List X) -> List X
mkList = <_>
{-
mkList (inl <>) = []
mkList (inr (x , xs)) = x ,- xs
-}
{-)-}

{-(-}
foldr : {X T : Set} -> ((ListF X) T -> T) -> List X -> T
foldr alg []        = alg (inl <>)
foldr alg (x ,- xs) = alg (inr (x , foldr alg xs))

ex1 = foldr mkList (1 ,- 2 ,- 3 ,- [])
{-)-}

{-(-}
length : {X : Set} -> List X -> Nat
length = foldr \ { (inl <>) -> zero ; (inr (x , n)) -> suc n }
{-)-}

record CoList (X : Set) : Set where
  coinductive
  field
    force : (ListF X) (CoList X)
open CoList

{-(-}
[]~ : {X : Set} -> CoList X
force []~ = inl <>

_,~_ : {X : Set} -> X -> CoList X -> CoList X
force (x ,~ xs) = inr (x , xs)
infixr 4 _,~_
{-)-}

{-(-}
unfoldr : {X S : Set} -> (S -> (ListF X) S) -> S -> CoList X
force (unfoldr coalg s) with coalg s
force (unfoldr coalg s) | inl <>       = inl <>
force (unfoldr coalg s) | inr (x , s') = inr (x , unfoldr coalg s')

ex2 = unfoldr force (1 ,~ 2 ,~ 3 ,~ []~)
{-)-}

{-(-}
repeat : {X : Set} -> X -> CoList X
repeat = unfoldr \ x -> inr (x , x)
{-)-}

{-(-}
prefix : {X : Set} -> Nat -> CoList X -> List X
prefix zero xs = []
prefix (suc n) xs with force xs
prefix (suc n) xs | inl <> = []
prefix (suc n) xs | inr (x , xs') = x ,- prefix n xs'

ex2' = prefix 3 ex2
{-)-}

StreamF : Set -> Set -> Set
StreamF X S = X * S

data Funny (X : Set) : Set where
  <_> : (StreamF X) (Funny X) -> Funny X

funny : {X : Set} -> Funny X -> Zero
funny < x , xf > = funny xf

record Stream (X : Set) : Set where
  coinductive
  field
    hdTl : (StreamF X) (Stream X)
open Stream

{-(-}
forever : {X : Set} -> X -> Stream X
fst (hdTl (forever x)) = x
snd (hdTl (forever x)) = forever x
{-)-}

natsFrom : Nat -> Stream Nat
fst (hdTl (natsFrom n)) = n
snd (hdTl (natsFrom n)) = natsFrom (suc n)

sprefix : {X : Set} -> Nat -> Stream X -> List X -- could be Vec X n
sprefix zero xs = []
sprefix (suc n) xs with hdTl xs
sprefix (suc n) xs | x , xs' = x ,- sprefix n xs'

{-(-}
unfold : {X S : Set} -> (S -> X * S) -> S -> Stream X
hdTl (unfold coalg s) with coalg s
hdTl (unfold coalg s) | x , s' = x , unfold coalg s'
{-)-}

natsFrom' : Nat -> Stream Nat
natsFrom' = unfold \ n -> n , suc n

data Two : Set where tt ff : Two

So : Two -> Set
So tt = One
So ff = Zero

isSuc : Nat -> Two
isSuc zero = ff
isSuc (suc n) = tt

{-
div : (x y : Nat) -> So (isSuc y) -> Nat
div x zero ()
div x (suc y) p = {!!}
-}

data Poly (X : Set) : Set where
  var' : X -> Poly X
  konst' : Two -> Poly X
  _+'_ _*'_ : Poly X -> Poly X -> Poly X

Eval : {X : Set} -> (X -> Set) -> Poly X -> Set
Eval var (var' x) = var x
Eval var (konst' b) = So b
Eval var (p +' q) = Eval var p + Eval var q
Eval var (p *' q) = Eval var p * Eval var q

eval : {X : Set}(u v : X -> Set)(p : Poly X) ->
       ((x : X) -> u x -> v x) ->
       Eval u p -> Eval v p
eval u v (var' i) f x = f i x
eval u v (konst' b) f x = x
eval u v (p +' q) f (inl x) = inl (eval u v p f x)
eval u v (p +' q) f (inr x) = inr (eval u v q f x)
eval u v (p *' q) f (x , y) = eval u v p f x , eval u v q f y

data Mu (p : Poly One) : Set where
  <_> : Eval (\ _ -> Mu p) p -> Mu p

NatP : Poly One
NatP = konst' tt +' var' <>

NAT = Mu NatP

ze : NAT
ze = < (inl <>) >

su : NAT -> NAT
su n = < (inr n) >

TreeP : Poly One
TreeP = konst' tt +' (var' <> *' var' <>)

-- What's a one-hole context in a Mu P?

Diff : Poly One -> Poly One
Diff (var' x) = konst' tt
Diff (konst' x) = konst' ff
Diff (p +' q) = Diff p +' Diff q
Diff (p *' q) = (Diff p *' q) +' (p *' Diff q)

plug : {X : Set}(p : Poly One) ->
       X -> Eval (\ _ -> X) (Diff p) ->
       Eval (\ _ -> X) p
plug (var' <>) x <> = x
plug (konst' b) x ()
plug (p +' q) x (inl xp') = inl (plug p x xp')
plug (p +' q) x (inr xq') = inr (plug q x xq')
plug (p *' q) x (inl (xp' , xq)) = plug p x xp' , xq
plug (p *' q) x (inr (xp , xq')) = xp , plug q x xq'

Context : Poly One -> Set
Context p = List (Eval (\ _ -> Mu p) (Diff p))

plugs : (p : Poly One) -> Mu p -> Context p -> Mu p
plugs p t []          = t
plugs p t (t' ,- t's) = plugs p < plug p t t' > t's


TernaryP : Poly One
TernaryP = konst' tt +' (var' <> *' (var' <> *' var' <>))




fold : (p : Poly One){T : Set}
       -> (Eval (\ _ -> T) p -> T)
       -> Mu p -> T
fold p {T} alg < x > = alg (evalFold p x)
  where
    evalFold : (q : Poly One)  -> Eval (\ _ -> Mu p) q -> Eval (\ _ -> T) q
    evalFold (var' <>) x = fold p alg x
    evalFold (konst' b) x = x
    evalFold (q +' r) (inl y) = inl (evalFold q y)
    evalFold (q +' r) (inr y) = inr (evalFold r y)
    evalFold (q *' r) (y , z) = evalFold q y , evalFold r z

record Nu (p : Poly One) : Set where
  coinductive
  field
    out : Eval (\ _ -> Nu p) p




-- What's the connection between polynomials and containers?

_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> (I -> Set)
(S -:> T) i = S i -> T i

[_] : {I : Set} -> (I -> Set) -> Set
[ P ] = forall i -> P i    -- [_] {I} P = (i : I) -> P i

All : {X : Set} -> (X -> Set) -> (List X -> Set)
All P [] = One
All P (x ,- xs) = P x * All P xs

record _|>_ (I O : Set) : Set where
  field
    Cuts   : O -> Set                      -- given o : O, how may we cut it?
    inners : {o : O} -> Cuts o -> List I   -- given how we cut it, what are
                                           --   the shapes of its pieces?

record Cutting {I O}(C : I |> O)(P : I -> Set)(o : O) : Set where
  constructor _8><_               -- "scissors"
  open _|>_ C
  field
    cut     : Cuts o              -- we decide how to cut o
    pieces  : All P (inners cut)  -- then we give all the pieces.
infixr 3 _8><_

data Interior {I}(C : I |> I)(T : I -> Set)(i : I) : Set where
                                         -- either...
  tile : T i -> Interior C T i           -- we have a tile that fits, or...
  <_>  : Cutting C (Interior C T) i ->   -- ...we cut, then tile the pieces.
         Interior C T i


_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

polyCon : {I : Set} -> Poly I -> I |> One
_|>_.Cuts (polyCon p) <> = Eval (\ _ -> One) p
_|>_.inners (polyCon (var' i)) <> = i ,- []
_|>_.inners (polyCon (konst' x)) s = []
_|>_.inners (polyCon (p +' q)) (inl xp) = _|>_.inners (polyCon p) xp
_|>_.inners (polyCon (p +' q)) (inr xq) =  _|>_.inners (polyCon q) xq
_|>_.inners (polyCon (p *' q)) (sp , sq) =
  _|>_.inners (polyCon p) sp +L  _|>_.inners (polyCon q) sq


Choose : {I J : Set} -> (I -> Set) -> (J -> Set) -> (I + J) -> Set
Choose X Y (inl i) = X i
Choose X Y (inr j) = Y j

data MU {I           -- what sorts of "elements" do we store?
         J           -- what sorts of "nodes" do we have?
         : Set}
        (F : J -> Poly (I + J))    -- what is the structure of each sort of node?
        (X : I -> Set)             -- what are the elements?
        (j : J)                    -- what sort is the outermost node?
        : Set where
  <_> : Eval (Choose X (MU F X))   -- subnodes in recursive positions
             (F j)
    ->  MU F X j
        
VecF : Nat -> Poly (One + Nat)
VecF zero = konst' tt
VecF (suc n) = (var' (inl <>)) *' (var' (inr n))

VEC : Nat -> Set -> Set
VEC n X = MU VecF (\ _ -> X) n

vnil : {X : Set} -> VEC zero X
vnil = < <> >

vcons : {X : Set}{n : Nat} -> X -> VEC n X -> VEC (suc n) X
vcons x xs = < (x , xs) >

gmap : {I           -- what sorts of "elements" do we store?
         J           -- what sorts of "nodes" do we have?
         : Set}
        {F : J -> Poly (I + J)}    -- what is the structure of each sort of node?
        {X Y : I -> Set} ->             -- what are the elements?
        ((i : I) -> X i -> Y i) ->
        (j : J) ->
        MU F X j -> MU F Y j
gmapHelp : ∀ {I J} (F : J → Poly (I + J)) {X Y : I → Set}
             (w : Poly (I + J)) →
           ((i : I) → X i → Y i) →
           Eval (Choose X (MU F X)) w →
           Eval (Choose Y (MU F Y)) w
gmap {F = F} f j < xt > = < gmapHelp F (F j) f xt >
gmapHelp F (var' (inl i)) f x = f i x
gmapHelp F (var' (inr j)) f t = gmap f j t
gmapHelp F (konst' x) f v = v
gmapHelp F (p +' q) f (inl xp) = inl (gmapHelp F p f xp)
gmapHelp F (p +' q) f (inr xq) = inr (gmapHelp F q f xq)
gmapHelp F (p *' q) f (xp , xq) = (gmapHelp F p f xp) , (gmapHelp F q f xq)
