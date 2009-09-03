module Main where
import Data.Queue

get_words = do
              s <- getContents
              return (words s)

enqueue_all [] q = q
enqueue_all (w:l) q = enqueue_all l (enqueue q w)

main :: IO ()
main = do 
          w <- get_words
          q <- enqueue_all w newFifo
          r <- (dequeue q) 
          x <- (case r of
                  Just(s) -> s)
          (putStrLn x)


