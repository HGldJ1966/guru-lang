module Main where
import Control.Concurrent
import Data.Queue


get_words = do
              s <- getContents
              return (words s)


enqueue_all (w:[]) q = enqueue q w
enqueue_all (w:l) q = do
  enqueue q w
  enqueue_all l q


main :: IO ()
main = do 
          w <- get_words
          q <- (newFifo::IO (MVar String))
          enqueue q (head w)
          --enqueue q (head (tail w))
          r <- (dequeue q) 
          myPrint r
    where 
      myPrint (Just x) = putStrLn x
      myPrint Nothing = putStrLn "oops"


