module ANSIEscapes where

data Dir = DU | DD | DL | DR

instance Show Dir where
  show DU   = "A"
  show DD   = "B"
  show DR   = "C"
  show DL   = "D"

upLine            = putStr "\ESC[1A"
downLine          = putStr "\ESC[1B"

up                = moveCursor DU
down              = moveCursor DD
backward          = moveCursor DL
forward           = moveCursor DR

moveCursor        :: Dir -> Int -> IO ()
moveCursor dir 0  = return ()
moveCursor dir n  = putStr $ "\ESC[" ++ show n ++ show dir

killLine          = escape "K" 
restoreCursor     = escape "u"
saveCursor        = escape "s"
clearScreen       = escape "2J"
initTermSize      = (escape "[=3h")

resetCursor       = escape "0;0H"

escape e          = putStr $ "\ESC[" ++ e

yellow str        = "\ESC[1;33m" ++ str ++ "\ESC[0m"
brown str         = "\ESC[0;33m" ++ str ++ "\ESC[0m"  
blue str          = "\ESC[1;34m" ++ str ++ "\ESC[0m"  
red str           = "\ESC[1;31m" ++ str ++ "\ESC[0m"  
green str         = "\ESC[1;32m" ++ str ++ "\ESC[0m"
purple str        = "\ESC[1;35m" ++ str ++ "\ESC[0m"
white str         = "\ESC[37m" ++ str ++ "\ESC[0m"



--Be careful, these assume someone else will reset the background colour
yellowOnGrey str        = "\ESC[1;33m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"
brownOnGrey str         = "\ESC[0;33m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"  
blueOnGrey str          = "\ESC[1;34m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"  
redOnGrey str           = "\ESC[1;31m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"  
greenOnGrey str         = "\ESC[1;32m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"
purpleOnGrey str        = "\ESC[1;35m\ESC[47m" ++ str ++ "\ESC[0m\ESC[47m"
whiteOnGrey str         = "\ESC[37m" ++ str ++ "\ESC[0m"

onBlack str       = "\ESC[40m" ++ str ++ "\ESC[0m"
onGrey str        = onGreyEsc ++ str ++ onWhiteEsc
onGreyEsc         = "\ESC[47m"
onWhiteEsc        = "\ESC[0m"
orange str        = str    