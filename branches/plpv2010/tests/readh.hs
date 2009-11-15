module Main where

import Data.Char 

main = do
        s <- getContents
        cat s

cat [c] = do 
                putChar c
		return ()
cat (c:cs) = do 
		cat cs
cat [] = return ()
