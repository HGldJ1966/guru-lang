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

mass_dequeue q 1 = dequeue q 
mass_dequeue q n = do
  dequeue q
  mass_dequeue q (n-1)

main :: IO ()
main = do 
          w <- get_words
          q <- (newFifo::IO (TChan String))
          enqueue_all w q
          mass_dequeue q ((length w) - 1) --dequeues all but last word using length of w as guide
          r <- (dequeue q) 
          myPrint r
    where 
      myPrint (Just x) = putStrLn x
      myPrint Nothing = putStrLn "oops"


