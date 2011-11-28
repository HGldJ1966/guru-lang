module Main where
import GHC.Arr
import Data.Word

mylt a b = (a < b)

myeq a b = (a == b)

data MyComp = MGT | MEQ | MLT deriving (Show,Eq)

comparator :: (Word32 -> Word32 -> Bool) -> 
              (Word32 -> Word32 -> Bool) ->
              Word32 -> Word32 -> MyComp
comparator lt le a b = case (lt a b) of
                         False -> case (le a b) of
                                    False -> MGT
                                    True -> MEQ
                         True -> MLT

binary_search :: Word32 -> Word32 -> Array Word32 Word32 -> Word32 -> Bool
binary_search f l arr v =
    case (comparator mylt myeq (arr!mid) v) of
      MLT -> if ((mid + 1) <= l) 
            then binary_search (mid + 1) l arr v
            else False
      MGT -> if (f <= (mid - 1))
            then binary_search f (mid - 1) arr v
            else False
      MEQ -> True
    where mid = f + ((l - f) `div` 2)
                        

main :: IO ()
main = putStrLn (show test)
    where size = 1048576 --2^20
          arr = array (1, size) [(i, i) | i <- [1..size]]
          test = and [binary_search 1 size arr x | x <- [1..size]]