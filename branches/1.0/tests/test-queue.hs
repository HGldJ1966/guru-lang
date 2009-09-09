module Main where
import Control.Concurrent
import Data.Queue
import Data.Maybe


get_words = do
              s <- getContents
              return (words s)


enqueue_all (w:[]) q = enqueue q w
enqueue_all (w:l) q = do
  enqueue q w
  enqueue_all l q

requeue q1 q2 1 = do
  r <- dequeue q1
  enqueue q2 (fromJust r)
requeue q1 q2 n = do
  r <- dequeue q1
  enqueue q2 (fromJust r)
  requeue q1 q2 (n-1)

mass_dequeue q 1 = dequeue q 
mass_dequeue q n = do
  dequeue q
  mass_dequeue q (n-1)

main :: IO ()
main = do 
          w <- get_words
          q1 <- (newFifo::IO (TChan String))
          q2 <- (newFifo::IO (TChan String))
          enqueue_all w q1
          requeue q1 q2 (length w)
          mass_dequeue q2 ((length w) - 1) --dequeues all but last word using length of w as guide
          r <- (dequeue q2) 
          myPrint r
    where 
      myPrint (Just x) = putStrLn x
      myPrint Nothing = putStrLn "oops"


