{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE TupleSections     #-}

module Data.Vector.Sort.Radix where

import           Data.Bits
import qualified Data.Foldable               as F
import           Data.Word
import           GHC.Exts
import           Unsafe.Coerce
import qualified GHC.Integer.GMP.Internals   as GMP
import qualified Data.Vector.Unboxed         as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

-------------------------------------------------------------------------------
-- radix sort
-------------------------------------------------------------------------------
radixSort64 :: VU.Vector Word64 -> VU.Vector Word64
radixSort64 vword = F.foldl' step vword ([0,16,32,48] :: [Int])
  where
    mask k x = fromIntegral $ x .>>. k .&. 0xffff
    step v k = VU.create $ do
      pref <- VU.unsafeThaw
            . VU.prescanl' (+) 0
            . VU.unsafeAccumulate (+) (VU.replicate 0x10000 0)
            $ VU.map ((, 1) . mask k) v
      res <- VUM.unsafeNew $ VU.length v
      VU.forM_ v $ \x -> do
        let !masked = mask k x
        i <- VUM.unsafeRead pref masked
        VUM.unsafeWrite pref masked $ i + 1
        VUM.unsafeWrite res i x
      return res
{-# INLINE radixSort64 #-}

radixSort :: (VU.Unbox a, Word64Encode a) => VU.Vector a -> VU.Vector a
radixSort = VU.map decode64 . radixSort64 . VU.map encode64
{-# INLINE radixSort #-}

radixSortInt :: VU.Vector Int -> VU.Vector Int
radixSortInt = unsafeCoerce . radixSort64 . unsafeCoerce

radixSortNonNegative :: (VU.Unbox a, Word64Encode a) => VU.Vector a -> VU.Vector a
radixSortNonNegative = VU.map decodeNonNegative64 . radixSort64 . VU.map encodeNonNegative64
{-# INLINE radixSortNonNegative #-}

radixSort32 :: VU.Vector Word32 -> VU.Vector Word32
radixSort32 vec = F.foldl' step vec ([0, 16] :: [Int])
  where
    mask k x = fromIntegral $ x .>>. k .&. 0xffff
    step v k = VU.create $ do
      pref <- VU.unsafeThaw
            . VU.prescanl' (+) 0
            . VU.unsafeAccumulate (+) (VU.replicate 0x10000 0)
            $ VU.map ((, 1) . mask k) v
      res <- VUM.unsafeNew $ VU.length v
      VU.forM_ v $ \x -> do
        let !masked = mask k x
        i <- VUM.unsafeRead pref masked
        VUM.unsafeWrite pref masked $ i + 1
        VUM.unsafeWrite res i x
      return res
{-# INLINE radixSort32 #-}

compress :: VU.Vector Int -> VU.Vector Int
compress vec = VU.create $ do
  mvec <- VUM.unsafeNew (VU.length vec)
  VU.mapM_ (\(i, x) -> VUM.unsafeWrite mvec (x .&. 0xffffffff) i) . VU.postscanl' (\(!i, !x) y ->
        if x .>>. 32 == y .>>. 32
          then (i, y)
          else (i + 1, y)
      ) (-1, -1)
    . radixSortInt
    $ VU.imap (\i x -> x .<<. 32 .|. i) vec
  return mvec
{-# INLINE compress #-}

class Word64Encode a where
  encode64 :: a -> Word64
  decode64 :: Word64 -> a
  encodeNonNegative64 :: a -> Word64
  encodeNonNegative64 = encode64
  decodeNonNegative64 :: Word64 -> a
  decodeNonNegative64 = decode64

instance Word64Encode Int where
  encode64 x = unsafeCoerce $ x + 0x3fffffffffffffff
  decode64 x = unsafeCoerce x - 0x3fffffffffffffff
  encodeNonNegative64 = unsafeCoerce
  decodeNonNegative64 = unsafeCoerce

instance Word64Encode (Int, Int) where
  encode64 (x, y) = unsafeCoerce
    $ (x + 0x3fffffff) .<<. 31 .|. (y + 0x3fffffff)
  decode64 xy = unsafeCoerce (x, y)
    where
      !x = xy .>>. 31 - 0x3fffffff
      !y = (xy .&. 0x7fffffff) - 0x3fffffff
  encodeNonNegative64 (x, y) = unsafeCoerce $ x .<<. 31 .|. y
  decodeNonNegative64 xy     = unsafeCoerce (x, y)
    where
      !x = xy .>>. 31
      !y = xy .&. 0x7fffffff

instance Word64Encode (Int, Int, Int) where
  encode64 (x, y, z) = unsafeCoerce $ ((x + 0xfffff) .<<. 21 .|. (y + 0xfffff)) .<<. 21 .|. (z + 0xfffff)
  decode64 xyz = unsafeCoerce (x, y, z)
    where
      !x = xyz .>>. 42 - 0xfffff
      !y = (xyz .>>. 21 .&. 0x1fffff) - 0xfffff
      !z = xyz .&. 0x1fffff - 0xfffff
  encodeNonNegative64 (x, y, z) = unsafeCoerce $ (x .<<. 21 .|. y) .<<. 21 .|. z
  decodeNonNegative64 xyz = unsafeCoerce (x, y, z)
    where
      !x = xyz .>>. 42
      !y = xyz .>>. 21 .&. 0x1fffff
      !z = xyz .&. 0x1fffff

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