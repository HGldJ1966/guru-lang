module Main where
import Data.Sequence


get_words = do
              s <- getContents
              return (words s)


enqueue_all :: [String] -> Seq String -> Seq String
enqueue_all (w:[]) q = q |> w
enqueue_all (w:l) q = enqueue_all l $! q |> w

requeue_all :: Int -> Seq String -> Seq String -> Seq String
requeue_all 0 _ r = r
requeue_all n q r = requeue_all (n - 1) q $! r |> (index q n)

main :: IO ()
main = do
  w <- get_words

  putStrLn (let x = (enqueue_all w q) in
            let y = (requeue_all (Data.Sequence.length x) x r) in
            let z = (requeue_all (Data.Sequence.length y) y s) in
            let aa = (requeue_all (Data.Sequence.length z) z t) in
              (index aa 1))
{-
  putStrLn (let x = (enqueue_all w q) in
            (index x ((Data.Sequence.length x) - 1)))
-}
  where
    q = empty::Seq String
    r = empty::Seq String
    s = empty::Seq String
    t = empty::Seq String
