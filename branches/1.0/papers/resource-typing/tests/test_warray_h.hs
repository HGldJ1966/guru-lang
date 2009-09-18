module Main where
import GHC.Arr
import Data.Word

binary_search :: Word32 -> Word32 -> Array Word32 Word32 -> Word32 -> Bool
binary_search f l arr v
    | arr!mid < v = if ((mid + 1) <= l) 
                    then binary_search (mid + 1) l arr v
                    else False
    | arr!mid > v = if (f <= (mid - 1))
                    then binary_search f (mid - 1) arr v
                    else False
    | otherwise = True
    where mid = f + ((l - f) `div` 2)
                        

main :: IO ()
main = putStrLn (show test)
    where size = 1048576 --2^20
          arr = array (1, size) [(i, i) | i <- [1..size]]
          test = and [binary_search 1 size arr x | x <- [1..size]]