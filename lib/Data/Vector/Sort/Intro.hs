{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE MagicHash        #-}

module Data.Vector.Sort.Intro where

import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Data.Bits
import           Data.Word
import           GHC.Exts
import           Unsafe.Coerce
import qualified GHC.Integer.GMP.Internals         as GMP
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Generic               as VG
import qualified Data.Vector.Generic.Mutable       as VGM

-------------------------------------------------------------------------------
-- intro sort
-------------------------------------------------------------------------------
introSort :: (Ord a, VG.Vector v a) => v a -> v a
introSort = introSortBy compare

introSortBy :: VG.Vector v a => (a -> a -> Ordering) -> v a -> v a
introSortBy cmp = VG.modify $ inplaceIntroSortBy cmp

inplaceIntroSortBy :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> ST s ()
inplaceIntroSortBy cmp vec = do
  let depthLimit = 2 * floorLog2 (VGM.length vec)
      threshold  = 16
  fix `flip` depthLimit `flip` vec $ \loop !depth mv ->
    when (VGM.length mv > threshold) $
      if depth > 0
        then do
          pivot <- getMedian3Pivot cmp mv
          cut   <- pivotPartition  cmp mv pivot
          loop (depth - 1) (VGM.unsafeDrop cut mv)
          loop (depth - 1) (VGM.unsafeTake cut mv)
        else inplaceHeapSortBy cmp mv
  inplaceInsertionSortBy cmp vec
  where
    floorLog2 :: Int -> Int
    floorLog2 x = fromIntegral $ y .>>. 52 - 1023
      where
        y :: Word64
        y = unsafeCoerce (fromIntegral x :: Double)

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

inplaceInsertionSortBy :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> ST s ()
inplaceInsertionSortBy cmp vec =
  rep1 (VGM.length vec) $ \i -> do
    x  <- VGM.unsafeRead vec i
    hd <- VGM.unsafeRead vec 0
    case cmp hd x of
      LT -> flip fix i $ \loop !j -> do
        y <- VGM.unsafeRead vec (j - 1)
        case cmp x y of
          LT -> do
            VGM.unsafeWrite vec j y
            loop (j - 1)
          _  -> VGM.unsafeWrite vec j x
      _  -> flip fix i $ \loop !j ->
        if j > 0
          then do
            VGM.unsafeRead vec (j - 1) >>= VGM.unsafeWrite vec j
            loop (j - 1)
          else VGM.unsafeWrite vec 0 x
{-# INLINE inplaceInsertionSortBy #-}

siftDown :: VGM.MVector mv a => (a -> a -> Ordering) -> Int -> mv s a -> ST s ()
siftDown cmp offset vec = do
  let !len = VGM.length vec
  flip fix offset $ \loop !parent -> do
    let !l = 2 * parent + 1
        !r = l + 1
    x <- VGM.unsafeRead vec parent
    when (l < len) $ do
      childL <- VGM.unsafeRead vec l
      if r < len
        then do
          childR <- VGM.unsafeRead vec r
          case cmp childL childR of
            LT -> when (cmp x childR == LT) $ do
              VGM.unsafeSwap vec parent r
              loop r
            _  -> when (cmp x childL == LT) $ do
              VGM.unsafeSwap vec parent l
              loop l
        else when (cmp x childL == LT) $ do
          VGM.unsafeSwap vec parent l
          loop l
{-# INLINE siftDown #-}

heapify :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> ST s ()
heapify cmp vec = rev (VGM.length vec `quot` 2) $ \i -> siftDown cmp i vec
{-# INLINE heapify #-}

inplaceHeapSortBy :: VGM.MVector mv a => (a -> a -> Ordering) -> mv s a -> ST s ()
inplaceHeapSortBy cmp vec = do
  heapify cmp vec
  flip fix (VGM.length vec - 1) $ \loop !i ->
    when (i > 0) $ do
      VGM.unsafeSwap vec 0 i
      siftDown cmp 0 $ VGM.unsafeTake i vec
      loop (i - 1)
{-# INLINE inplaceHeapSortBy #-}

-------------------------------------------------------------------------------
-- for
-------------------------------------------------------------------------------
rep :: Monad m => Int -> (Int -> m ()) -> m ()
rep n = flip VFSM.mapM_ (streamG 0 (n - 1) const 0 (+) 1)
{-# INLINE rep #-}

rep' :: Monad m => Int -> (Int -> m ()) -> m ()
rep' n = flip VFSM.mapM_ (streamG 0 n const 0 (+) 1)
{-# INLINE rep' #-}

rep1 :: Monad m => Int -> (Int -> m ()) -> m ()
rep1 n = flip VFSM.mapM_ (streamG 1 (n - 1) const 0 (+) 1)
{-# INLINE rep1 #-}

rep1' :: Monad m => Int -> (Int -> m ()) -> m ()
rep1' n = flip VFSM.mapM_ (streamG 1 n const 0 (+) 1)
{-# INLINE rep1' #-}

rev :: Monad m => Int -> (Int -> m ()) -> m ()
rev n = flip VFSM.mapM_ (streamRG (n - 1) 0 const 0 (-) 1)
{-# INLINE rev #-}

rev' :: Monad m => Int -> (Int -> m ()) -> m ()
rev' n = flip VFSM.mapM_ (streamRG n 0 const 0 (-) 1)
{-# INLINE rev' #-}

rev1 :: Monad m => Int -> (Int -> m ()) -> m ()
rev1 n = flip VFSM.mapM_ (streamRG (n - 1) 1 const 0 (-) 1)
{-# INLINE rev1 #-}

rev1' :: Monad m => Int -> (Int -> m ()) -> m ()
rev1' n = flip VFSM.mapM_ (streamRG n 1 const 0 (-) 1)
{-# INLINE rev1' #-}

range :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
range l r = flip VFSM.mapM_ (streamG l r const 0 (+) 1)
{-# INLINE range #-}

rangeR :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
rangeR r l = flip VFSM.mapM_ (streamRG r l const 0 (-) 1)
{-# INLINE rangeR #-}

forP :: Monad m => Int -> (Int -> m ()) -> m ()
forP p = flip VFSM.mapM_ (streamG 2 p (^) 2 (+) 1)
{-# INLINE forP #-}

forG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forG l r f p g d = flip VFSM.mapM_ (streamG l r f p g d)
{-# INLINE forG #-}

forRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forRG r l f p g d = flip VFSM.mapM_ (streamRG r l f p g d)
{-# INLINE forRG #-}

streamG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> VFSM.Stream m Int
streamG !l !r !f !p !g !d = VFSM.Stream step l
  where
    step x
      | f x p <= r = return $ VFSM.Yield x (g x d)
      | otherwise  = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamG #-}

streamRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> VFSM.Stream m Int
streamRG !r !l !f !p !g !d = VFSM.Stream step r
  where
    step x
      | f x p >= l = return $ VFSM.Yield x (g x d)
      | otherwise  = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamRG #-}

withBreakIO :: ((r -> ContT r IO b) -> ContT r IO r) -> IO r
withBreakIO = flip runContT pure . callCC
{-# INLINE withBreakIO #-}

withBreakST :: ((r -> ContT r (ST s) b) -> ContT r (ST s) r) -> (ST s) r
withBreakST = flip runContT pure . callCC
{-# INLINE withBreakST #-}

-------------------------------------------------------------------------------
-- util
-------------------------------------------------------------------------------
fi :: Int -> Integer
fi = fromIntegral
{-# INLINE fi #-}

fI :: Integer -> Int
fI = fromInteger
{-# INLINE fI #-}

powModInt :: Int -> Int -> Int -> Int
powModInt a b c = fI $ GMP.powModInteger (fi a) (fi b) (fi c)
{-# INLINE powModInt #-}

recipModInt :: Int -> Int -> Int
recipModInt a m = fI $ GMP.recipModInteger (fi a) (fi m)
{-# INLINE recipModInt #-}

infixl 8 .<<., .>>., .>>>.
infixl 6 .^.

(.<<.) :: Bits b => b -> Int -> b
(.<<.) = unsafeShiftL
{-# INLINE (.<<.) #-}

(.>>.) :: Bits b => b -> Int -> b
(.>>.) = unsafeShiftR
{-# INLINE (.>>.) #-}

(.>>>.) :: Int -> Int -> Int
(.>>>.) (I# x#) (I# i#) = I# (uncheckedIShiftRL# x# i#)
{-# INLINE (.>>>.) #-}

(.^.) :: Bits b => b -> b -> b
(.^.)  = xor
{-# INLINE (.^.)  #-}

clz :: FiniteBits fb => fb -> Int
clz = countLeadingZeros
{-# INLINE clz #-}

ctz :: FiniteBits fb => fb -> Int
ctz = countTrailingZeros
{-# INLINE ctz #-}

encode32x2 :: Int -> Int -> Int
encode32x2 x y = x .<<. 32 .|. y
{-# INLINE encode32x2 #-}

decode32x2 :: Int -> (Int, Int)
decode32x2 xy =
    let !x = xy .>>>. 32
        !y = xy .&. 0xffffffff
    in (x, y)
{-# INLINE decode32x2 #-}

ceilPow2 :: Int -> Int
ceilPow2 n
  | n > 1     = (-1) .>>>. clz (n - 1) + 1
  | otherwise = 1
{-# INLINE ceilPow2 #-}

floorPow2 :: Int -> Int
floorPow2 n
  | n >= 1    = 1 .<<. (63 - clz n)
  | otherwise = 0
{-# INLINE floorPow2 #-}

bitReverse :: Int -> Int
bitReverse
  = unsafeCoerce
  . step 32 0xffffffff00000000 0x00000000ffffffff
  . step 16 0xffff0000ffff0000 0x0000ffff0000ffff
  . step 08 0xff00ff00ff00ff00 0x00ff00ff00ff00ff
  . step 04 0xf0f0f0f0f0f0f0f0 0x0f0f0f0f0f0f0f0f
  . step 02 0xcccccccccccccccc 0x3333333333333333
  . step 01 0xaaaaaaaaaaaaaaaa 0x5555555555555555
  . unsafeCoerce
  where
    step :: Int -> Word64 -> Word64 -> Word64 -> Word64
    step i ml mr = \ !x -> (x .&. ml) .>>. i .|. (x .&. mr) .<<. i
    {-# INLINE step #-}