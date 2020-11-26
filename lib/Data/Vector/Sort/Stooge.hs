module Data.Vector.Sort.Stooge where

import           Control.Monad
import           Control.Monad.Fix
import qualified Data.Vector.Generic         as VG
import qualified Data.Vector.Generic.Mutable as VGM

-------------------------------------------------------------------------------
-- stooge sort
-------------------------------------------------------------------------------
stoogeSort :: (Ord a, VG.Vector v a) => v a -> v a
stoogeSort = stoogeSortBy compare

stoogeSortBy :: (Ord a, VG.Vector v a) => (a -> a -> Ordering) -> v a -> v a
stoogeSortBy cmp = VG.modify $ fix $ \loop vec -> do
  item1 <- VGM.unsafeRead vec 0
  item2 <- VGM.unsafeRead vec (VGM.length vec - 1)
  when (cmp item1 item2 == GT) $ VGM.unsafeSwap vec 0 (VGM.length vec - 1)
  when (VGM.length vec > 2) $ do
    loop (VGM.unsafeTake ((VGM.length vec `div` 3) * 2) vec)
    loop (VGM.unsafeDrop  (VGM.length vec `div` 3)      vec)
    loop (VGM.unsafeTake ((VGM.length vec `div` 3) * 2) vec)
{-# INLINE stoogeSortBy #-}