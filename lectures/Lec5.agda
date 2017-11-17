module Lec5 where


open import Lec1Done
open import Lec2Done
open import Lec3Done


data List (X : Set) : Set where -- BUILTIN insists on level polymorphism
  []   : List X
  _,-_ : (x : X)(xs : List X) -> List X
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _,-_ #-}
{-# COMPILE GHC List = data [] ([] | (:)) #-}

list : {X Y : Set} -> (X -> Y) -> List X -> List Y
list f []         = []
list f (x ,- xs)  = f x ,- list f xs

data Two : Set where ff tt : Two
{-# BUILTIN BOOL Two #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN TRUE tt #-}


----------------------------------------------------------------------------
-- chars and strings
----------------------------------------------------------------------------

postulate       -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String


---------------------------------------------------------------------------
-- COLOURS
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour
{-# COMPILE GHC Colour = data HaskellSetup.Colour (HaskellSetup.Black | HaskellSetup.Red | HaskellSetup.Green | HaskellSetup.Yellow | HaskellSetup.Blue | HaskellSetup.Magenta | HaskellSetup.Cyan | HaskellSetup.White) #-}

record _**_ (S T : Set) : Set where
  constructor _,_
  field
    outl : S
    outr : T
open _**_
{-# COMPILE GHC _**_ = data (,) ((,)) #-}
infixr 4 _**_ _,_

{- Here's the characterization of keys I give you -}
data Direction : Set where up down left right : Direction
data Modifier : Set where normal shift control : Modifier
data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key
data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : Nat) -> Event

{- This type collects the things you're allowed to do with the text window. -}
data Action : Set where
  goRowCol : Nat -> Nat -> Action    -- send the cursor somewhere
  sendText : List Char -> Action     -- send some text
  move     : Direction -> Nat -> Action  -- which way and how much
  fgText   : Colour -> Action
  bgText   : Colour -> Action

{- I wire all of that stuff up to its Haskell counterpart. -}
{-# FOREIGN GHC import qualified ANSIEscapes #-}
{-# FOREIGN GHC import qualified HaskellSetup #-}
{-# COMPILE GHC Direction = data ANSIEscapes.Dir (ANSIEscapes.DU | ANSIEscapes.DD | ANSIEscapes.DL | ANSIEscapes.DR) #-}
{-# COMPILE GHC Modifier = data HaskellSetup.Modifier (HaskellSetup.Normal | HaskellSetup.Shift | HaskellSetup.Control) #-}
{-# COMPILE GHC Key = data HaskellSetup.Key (HaskellSetup.Char | HaskellSetup.Arrow | HaskellSetup.Enter | HaskellSetup.Backspace | HaskellSetup.Delete | HaskellSetup.Escape | HaskellSetup.Tab) #-}
{-# COMPILE GHC Event = data HaskellSetup.Event (HaskellSetup.Key | HaskellSetup.Resize) #-}
{-# COMPILE GHC Action = data HaskellSetup.Action (HaskellSetup.GoRowCol | HaskellSetup.SendText | HaskellSetup.Move | HaskellSetup.FgText | HaskellSetup.BgText) #-}


data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- ... e.g.     green - '*' / black    for a green * on black.

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h

Painting : Nat * Nat -> Set
Painting = Matrix ColourChar

vecFoldR : {X Y : Set} -> (X -> Y -> Y) -> Y -> {n : Nat} -> Vec X n -> Y
vecFoldR c n [] = n
vecFoldR c n (x ,- xs) = c x (vecFoldR c n xs)

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction = vecFoldR (vecFoldR (\ {(f - c / b) k -> \ as ->
  fgText f ,- bgText b ,- sendText (c ,- []) ,- k as}) id) []


postulate       -- Haskell has a monad for doing IO, which we use at the top level
  IO      : Set -> Set
  return  : {A : Set} -> A -> IO A
  _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
infixl 1 _>>=_
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC return = (\ _ -> return) #-}
{-# COMPILE GHC _>>=_ = (\ _ _ -> (>>=)) #-}


---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Application (wh : Nat * Nat) : Set where
  coinductive
  field
    handleKey     : Key -> Application wh
    handleResize  : (wh' : Nat * Nat) -> Application wh'
    paintMe       : Painting wh
    cursorMe      : Nat * Nat  -- x,y coords
open Application public

-- Now your turn. Build the appropriate handler to connect these
-- applications with mainAppLoop. Again, work in two stages, first
-- figuring out how to do the right actions, then managing the
-- state properly. (1 mark)

_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
infixr 3 _+L_

APP : Set
APP = Sg (Nat * Nat) Application

appPaint : APP -> List Action
appPaint (_ , app) =
  goRowCol 0 0 ,- paintAction p
     -- must have composition here, to work around compiler bug
     -- paintAction (paintMatrix p)
     -- segfaults, because p is erased
  +L (goRowCol (snd xy) (fst xy) ,- [])
  where
    p  = paintMe app
    xy = cursorMe app

appHandler : Event -> APP -> APP ** List Action
appHandler (key k) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleKey app k
appHandler (resize w h) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleResize app (w , h)

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILE GHC mainAppLoop = (\ _ -> HaskellSetup.mainAppLoop) #-}

appMain : (forall wh -> Application wh) -> IO One
appMain app = mainAppLoop ((0 , 0) , app (0 , 0)) appHandler
  -- will get resized dynamically to size of terminal, first thing

vPure : {n : Nat}{X : Set} -> X -> Vec X n
vPure {zero} x = []
vPure {suc n} x = x ,- vPure x

rectApp : Char -> forall wh -> Application wh
handleKey (rectApp c wh) (char x) = rectApp x wh
handleKey (rectApp c wh) _ = rectApp c wh
handleResize (rectApp c _)  wh = rectApp c wh
paintMe      (rectApp c wh)    = vPure (vPure (green - c / black))
cursorMe     (rectApp c wh)    = wh

main : IO One
main = appMain (rectApp '*')

--  agda --compile --ghc-flag "-lncurses" Lec5.agda
