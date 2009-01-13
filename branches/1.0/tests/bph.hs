module Main where

import Control.Exception 
import System( getArgs )

main = do
        args <- getArgs
        s <- getContents
        putStrLn (show (balanced s Z))

data Nat = Z | Succ Nat

loop = loop

balanced ('(':cs) n = balanced cs (Succ n)
balanced (')':cs) (Succ n) = balanced cs n
balanced (_:cs) n = balanced cs n
balanced [] Z = True
balanced [] _ = False 
