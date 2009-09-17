module Main where
import Data.Sequence


get_words = do
              s <- getContents
              return (words s)


enqueue_all :: [String] -> Seq String -> Seq String
enqueue_all (w:[]) q = q |> w
enqueue_all (w:l) q = enqueue_all l $! q |> w



main :: IO ()
main = do
  w <- get_words
  putStrLn (let x = (enqueue_all w q) in
              (index x ((Data.Sequence.length x) - 1)))
  where
    q = empty::Seq String
