module Main where
import           Data.Vector.Sort.Intro
import qualified Data.Vector.Unboxed    as VU

xs :: VU.Vector (Int, Int, Int)
xs = VU.fromList ([(1,4,6), (5,2,5), (7,1,3), (2,6,2), (3,5,2), (1,2,5), (7,2,4), (3,5,2), (2,7,2), (3,1,6)] :: [(Int, Int, Int)])

main :: IO ()
main = print $ introSort xs