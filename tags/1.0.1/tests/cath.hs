module Main where

import Data.Char 

main = do
        s <- getContents
        cat s

cat (c:cs) = do 
                putChar c
		cat cs
cat [] = return ()
