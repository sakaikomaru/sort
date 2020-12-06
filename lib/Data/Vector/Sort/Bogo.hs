{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE TypeApplications #-}

module Data.Vector.Sort.Bogo where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Data.Bits
import           Data.STRef.Strict
import           Data.Word
import           GHC.Exts
import           System.CPUTime
import           Unsafe.Coerce
import qualified GHC.Integer.GMP.Internals         as GMP
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

-------------------------------------------------------------------------------
-- bogo sort
-------------------------------------------------------------------------------
bogoSort :: (Ord a, VU.Unbox a) => VU.Vector a -> IO (VU.Vector a)
bogoSort = bogoSortBy compare

bogoSortBy :: (Ord a, VU.Unbox a) => (a -> a -> Ordering) -> VU.Vector a -> IO (VU.Vector a)
bogoSortBy compare vec = do
  rng <- newRNG
  fix $ \loop -> do
    if isSorted compare vec
      then return vec
      else do
        shuffle rng vec
        loop

isSorted :: (Ord a, VU.Unbox a) => (a -> a -> Ordering) -> VU.Vector a -> Bool
isSorted comp vec = runST $ do
  ret <- newSTRef True
  rep (VU.length vec - 1) $ \i -> when (comp (vec VU.! i) (vec VU.! (i + 1)) /= LT) $ writeSTRef ret False
  readSTRef ret

-------------------------------------------------------------------------------
-- xorshift
-------------------------------------------------------------------------------
type RNG = VUM.IOVector Word64

getSeed :: IO Word64
getSeed = (* 0x3b47f24a) . fromInteger <$> getCPUTime
{-# NOINLINE getSeed #-}

newRNG :: IO RNG
newRNG = do
  x <- getSeed
  VUM.replicate 1 (8172645463325252 - x)
{-# NOINLINE newRNG #-}

nextWord64 :: RNG -> IO Word64
nextWord64 rng = do
  x <- VUM.unsafeRead rng 0
  let
    y = x .<<. 7 .^. x
    z = y .>>. 9 .^. y
  VUM.unsafeWrite rng 0 z
  return z

nextInt :: RNG -> IO Int
nextInt rng = unsafeCoerce <$> nextWord64 rng

nextDouble :: RNG -> IO Double
nextDouble rng = do
  t <- nextWord64 rng
  let x = 0x3ff .<<. 52 .|. t .>>. 12
  return $! unsafeCoerce @Word64 @Double x - 1.0

nextGauss :: RNG -> Double -> Double -> IO Double
nextGauss rng mu sigma = do
  x <- nextDouble rng
  y <- nextDouble rng
  let z = sqrt (-2.0 * log x) * cos (2.0 * pi * y)
  return $! sigma * z + mu

randomR :: RNG -> Int -> Int -> IO Int
randomR rng l r = (+ l) . flip mod (r - l + 1) <$> nextInt rng

shuffleM :: VUM.Unbox a => RNG -> VUM.IOVector a -> IO ()
shuffleM rng mvec = do
  rev (VUM.length mvec) $ \i -> do
    j <- nextWord64 rng
    VUM.unsafeSwap mvec i (unsafeCoerce $ rem j (unsafeCoerce i + 1))

shuffle :: VU.Unbox a => RNG -> VU.Vector a -> IO (VU.Vector a)
shuffle rng vec = do
  mv <- VU.unsafeThaw vec
  shuffleM rng mv
  VU.unsafeFreeze mv

-------------------------------------------------------------------------------
-- for
-------------------------------------------------------------------------------
rep :: Monad m => Int -> (Int -> m ()) -> m ()
rep n = flip VFSM.mapM_ (stream 0 n)
{-# INLINE rep #-}

rep' :: Monad m => Int -> (Int -> m ()) -> m ()
rep' n = flip VFSM.mapM_ (stream 0 (n + 1))
{-# INLINE rep' #-}

rep1 :: Monad m => Int -> (Int -> m ()) -> m ()
rep1 n = flip VFSM.mapM_ (stream 1 n)
{-# INLINE rep1 #-}

rep1' :: Monad m => Int -> (Int -> m ()) -> m ()
rep1' n = flip VFSM.mapM_ (stream 1 (n + 1))
{-# INLINE rep1' #-}

rev :: Monad m => Int -> (Int -> m ()) -> m ()
rev n = flip VFSM.mapM_ (streamR 0 n)
{-# INLINE rev #-}

rev' :: Monad m => Int -> (Int -> m ()) -> m ()
rev' n = flip VFSM.mapM_ (streamR 0 (n + 1))
{-# INLINE rev' #-}

rev1 :: Monad m => Int -> (Int -> m ()) -> m ()
rev1 n = flip VFSM.mapM_ (streamR 1 n)
{-# INLINE rev1 #-}

rev1' :: Monad m => Int -> (Int -> m ()) -> m ()
rev1' n = flip VFSM.mapM_ (streamR 1 (n + 1))
{-# INLINE rev1' #-}

range :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
range l r = flip VFSM.mapM_ (stream l (r + 1))
{-# INLINE range #-}

rangeR :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
rangeR r l = flip VFSM.mapM_ (streamR l (r + 1))
{-# INLINE rangeR #-}

forStep :: Monad m => Int -> Int -> Int -> (Int -> m ()) -> m ()
forStep l r d = flip VFSM.mapM_ (streamStep l r d)
{-# INLINE forStep #-}

forStepR :: Monad m => Int -> Int -> Int -> (Int -> m ()) -> m ()
forStepR r l d = flip VFSM.mapM_ (streamStepR l r d)
{-# INLINE forStepR #-}

forP :: Monad m => Int -> (Int -> m ()) -> m ()
forP p = flip VFSM.mapM_ (streamG 2 p (^) 2 (+) 1)
{-# INLINE forP #-}

forG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forG l r f p g d = flip VFSM.mapM_ (streamG l r f p g d)
{-# INLINE forG #-}

forRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forRG r l f p g d = flip VFSM.mapM_ (streamRG r l f p g d)
{-# INLINE forRG #-}

stream :: Monad m => Int -> Int -> VFSM.Stream m Int
stream !l !r = VFSM.Stream step l
  where
    step x
      | x < r     = return $ VFSM.Yield x (x + 1)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] stream #-}

streamR :: Monad m => Int -> Int -> VFSM.Stream m Int
streamR !l !r = VFSM.Stream step (r - 1)
  where
    step x
      | x >= l = return $ VFSM.Yield x (x - 1)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamR #-}

streamStep :: Monad m => Int -> Int -> Int -> VFSM.Stream m Int
streamStep !l !r !d = VFSM.Stream step l
  where
    step x
      | x <= r    = return $ VFSM.Yield x (x + d)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamStep #-}

streamStepR :: Monad m => Int -> Int -> Int -> VFSM.Stream m Int
streamStepR !l !r !d = VFSM.Stream step r
  where
    step x
      | x >= l    = return $ VFSM.Yield x (x - d)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamStepR #-}

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