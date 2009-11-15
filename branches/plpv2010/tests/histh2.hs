{- histogramming with fixed precision ints -}

module Main where

import Data.Array.IO 
import Data.Char 

main = do
        hist <- newArray (chr 0, chr 127) 0
        s <- getContents
        u <- do_hist2 hist s
        n <- readArray hist (chr 0)
        putStrLn (show n)

do_hist2 :: IOUArray Char Int -> [Char] -> IO ()

do_hist2 h (c:cs) = do 
                     n <- (readArray h c)
                     writeArray h c (n+1)
		     do_hist2 h cs
do_hist2 h [] = return ()
