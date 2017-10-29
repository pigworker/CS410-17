module Lec4HS where
import System.IO

mainLoop :: s -> (s -> Bool -> ([Bool], Maybe s)) -> IO ()
mainLoop s f = do
    hSetBuffering stdout NoBuffering
    hSetBuffering stdin NoBuffering
    hSetEcho stdin False
    innerLoop s
  where
    getBit = do
      c <- getChar
      case c of
        '0' -> return False
        '1' -> return True
        _   -> getBit
    innerLoop s = do
      b <- getBit
      let (os, ms) = f s b
      mapM_ (\ b -> if b then putChar '1' else putChar '0') os
      case ms of
        Just s -> innerLoop s
        Nothing -> return ()
        
mainOutIn :: s -> (s -> ([Bool], Maybe (Bool -> s))) -> IO ()
mainOutIn s f = do
    hSetBuffering stdout NoBuffering
    hSetBuffering stdin NoBuffering
    hSetEcho stdin False
    innerLoop s
  where
    getBit = do
      c <- getChar
      case c of
        '0' -> return False
        '1' -> return True
        _   -> getBit
    innerLoop s = do
      let (os, mk) = f s
      mapM_ (\ b -> if b then putChar '1' else putChar '0') os
      case mk of
        Just k -> do
          b <- getBit
          innerLoop (k b)
        Nothing -> return ()
