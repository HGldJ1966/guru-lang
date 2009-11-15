{- histogramming with unary nats. -}

module Main where

import Data.Array.IO 
import Data.Char 

main = do
        hist <- newArray (chr 0, chr 127) Z
        s <- getContents
        u <- do_hist hist s
        n <- readArray hist (chr 0)
        putStrLn (show n)

data Nat = Z | Succ Nat deriving Show

do_hist :: IOArray Char Nat -> [Char] -> IO ()

do_hist h (c:cs) = do 
                     n <- (readArray h c)
                     writeArray h c (Succ n)
		     do_hist h cs
do_hist h [] = return ()
