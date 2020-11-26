{-# LANGUAGE BangPatterns #-}

module Data.Vector.Sort.Quick where

import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.ST
import qualified Data.Vector.Generic         as VG
import qualified Data.Vector.Generic.Mutable as VGM

-------------------------------------------------------------------------------
-- quick sort
-------------------------------------------------------------------------------
quickSort :: (Ord a, VG.Vector v a) => v a -> v a
quickSort = quickSortBy compare

quickSortBy :: VG.Vector v a => (a -> a -> Ordering) -> v a -> v a
quickSortBy cmp = VG.modify $ fix $ \loop vec ->
  when (VGM.length vec > 1) $ do
    pivot <- getMedian3Pivot cmp vec
    cut   <- pivotPartition cmp vec pivot
    loop (VGM.unsafeDrop cut vec)
    loop (VGM.unsafeTake cut vec)
{-# INLINE quickSortBy #-}

pivotPartition :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> a -> ST s Int
pivotPartition cmp vec pivot = fix `flip` 0 `flip` VGM.length vec $ \loop !l !r -> do
  !l' <- flip fix l $ \loopL !i -> do
    x   <- VGM.unsafeRead vec i
    case cmp x pivot of
      LT -> loopL (i + 1)
      _  -> return i
  !r' <- flip fix (r - 1) $ \loopR !i -> do
    x <- VGM.unsafeRead vec i
    case cmp pivot x of
      LT -> loopR (i - 1)
      _  -> return i
  if l' < r'
    then do
      VGM.unsafeSwap vec l' r'
      loop (l' + 1) r'
    else return l'
{-# INLINE pivotPartition #-}

getMedian3Pivot :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> ST s a
getMedian3Pivot cmp vec = median cmp <$> VGM.unsafeRead vec 0 <*> VGM.unsafeRead vec (VGM.length vec `quot` 2) <*> VGM.unsafeRead vec (VGM.length vec - 1)
{-# INLINE getMedian3Pivot #-}

median :: (a -> a -> Ordering) -> a -> a -> a -> a
median cmp x y z = case cmp x y of
  LT -> case cmp y z of
    LT -> y
    _  -> case cmp x z of
      LT -> z
      _  -> x
  _  -> case cmp x z of
    LT -> x
    _  -> case cmp y z of
      LT -> z
      _  -> y
{-# INLINE median #-}