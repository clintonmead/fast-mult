{-# LANGUAGE MagicHash #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}

module Data.FastMult.Internal (FastMult(FastMult), FastMultSeq, simplify) where

#include "MachDeps.h"

import Prelude hiding (Integer)

import GHC.Integer.GMP.Internals (BigNat, Integer(S#, Jp#, Jn#), sizeofBigNat#, timesBigNat, bigNatToWord, wordToBigNat, wordToBigNat2)
import Data.Bits (FiniteBits, countLeadingZeros, finiteBitSize, xor, complement)
import GHC.Base (timesWord2#, Word(W#), int2Word#, Int(I#), eqWord#, (>=#), negateInt#)
import Data.Ord (comparing)
import Data.Strict.List ( List((:!)) )
import qualified Data.Strict.List as Strict
import GHC.TypeLits (Nat, KnownNat, natVal)
import GHC.Conc.Sync (par)
import Data.Proxy (Proxy)
import Data.Word (Word)
import Data.Ratio ((%))
import Data.Foldable (foldl')

-- We use 'Word' here not 'Bool' because it unpacks bette. I'm not sure if this is an optimisation.
newtype Sign = Sign Word deriving Show

pattern Pos = Sign 0
pattern Neg = Sign (-1)

multSigns :: Sign -> Sign -> Sign
multSigns (Sign x) (Sign y) = Sign (x `xor` y)

negateSign :: Sign -> Sign
negateSign (Sign x) = Sign (complement x)


data BigNatWithScale (n :: Nat) where
  BigNatWithScale :: KnownNat n => {-# UNPACK #-} !Word -> BigNat -> BigNatWithScale n

-- Internal debug only:
instance Show (BigNatWithScale n) where
  show (BigNatWithScale scale bigNat) = "(BigNatWithScale scale = " ++ show scale ++ ", num = " ++ show (Jp# bigNat) ++ ")"

getBigNat :: BigNatWithScale (n :: Nat) -> BigNat
getBigNat (BigNatWithScale _ x) = x

{-|
  'FastMult' is a Numeric type that can be used in any place a 'Num a' is required.
  It represents a standard integer using three components, which multiplied together represent the stored number:

  1. The number's sign
  2. An unsigned machine word.
  3. A (possibly empty) list of 'BigNat's, which are the internal type for 'Integer's which are too large to fit in a machine word.

  Each 'BigNat' in the list has a scale. It's scale is the log base 2 of the number of words to store the machine word, minus 1.

  Note that we never store BigNats with length of only one machine word in this list, we instead convert them to an ordinary
  unsigned machine word and multiply them by item 2 in the list above. Only then if the result overflows we place them in this
  'BigNat' list.

  This is a few examples of "MachineWords -> Scale"

  2 -> 0
  3 -> 1
  4 -> 1
  5 -> 2
  6..8 -> 2
  9..16 -> 3
  17..32 -> 4

  etc.

  Note this "scale" has the very nice property that multipling 'BigNat's of scale @x@ always results in a 'BigNat' of scale @x+1@.

  The list of 'BigNat's only ever contains one 'BigNat' of each "scale". As the size of 'BigNat's increases exponentially with scale,
  this list should always be relatively small. The 'BigNat' list is always sorted as well, smallest to largest.

  When we multiply two 'FastMult's, we merge the BigNat lists. This is basically a simple merge of sorted list,
  but with one significant change. Note that we said that the 'BigNat' list cannot contain two 'BigNat's of the same scale.
  So if find that a 'BigNat' in the left hand list of the multiplication is the same scale as a 'BigNat' in right hand list,
  we multiply these two 'BigNat's to create a 'BigNat' one "scale" larger. We then continue the merge, including this new BigNat.

  As a result, we only ever multiply numbers of the same "scale", that is, no more than double the length of one another.

  Why do we do this? Well, an ordinary product, say @product [1..1000000]@, towards the end of the list involves multiplications
  of a very large number by a machine word. These take @O(n)@ time. So the whole product takes @O(n^2)@ time.

  If we instead did the following:

  @
    product x y = product x mid * product mid y
      mid = (x + y) `div` 2

    (suitible base case here)
  @

  We find that this runs a lot faster. The reason is that with this approach we're minimising products involving very large numbers,
  and importantly, multiplying two @n@ length numbers doesn't take @O(n^2)@ but more like @O(n*log(n))@ time.
  For this reason it's better to do a few multiplication of large numbers by large numbers,
  instead of lots of multiplications of large numbers by small numbers.

  But to do this I've had to redefine product. What if you don't want to change the algorithm, but just want to use one that's
  already been written, perhaps inefficiently. Well this is where 'FastMult' is useful. Instead of making the algorithm smarter,
  'FastMult' just makes numbers smarter. The numbers themselves reorder the multiplications so you don't have too.

  As well as having the advantage of speeding up existing algorithms, 'FastMult' dynamically behaves differently based on
  what numbers it's actually multiplying and always maintains the invariant that multiplications will not be performed between
  numbers greater than twice the size each other.

  At this point I haven't mentioned the meaning of the `FastMult` type parameter @n@'. 'FastMult' can also add paralellism to
  your multiplication algorithms. However, sparking new GHC threads has a cost, so we only want to do it for large multiplications.
  Multiplications of @scale > n@ will spark a new thread, so @n = 0@ will spark new threads for any multiplication
  involving at least 3 machine words. This is probably too small, you can experiment with different numbers.
  Note that @n@ represents the scale, not size, so for example setting @n=4@ will only spark threads for multiplications involving
  at least 33 machine words.

  How well parallelism works (or if it works at all) hasn't been tested yet however.

  We include an ordinary machine word in the type as an optimisation for single machine word numbers.
  This is because multiplying 'BigNat's involves calling GMP using a C call, which is a large overhead for small multiplications.

  To use 'FastMult', all you have to do is import it's type, not it's implementation.
  If you're not interested in parallelism, just import 'FastMultSeq'.

  For example, just compare in GHCi:

  @
  product [1..100000]
  @

  and:

  @
  product [1::FastMultSeq..100000]
  @

  and you should find the latter completes much faster.

  Converting to and from 'Integer's can be done with the
  'toInteger' and 'fromInteger' class methods from 'Integral' and 'Num' respectively.
-}
data FastMult (n :: Nat) where
  FastMult :: KnownNat n => {-# UNPACK #-} !Sign -> {-# UNPACK #-} !Word -> !(Strict.List (BigNatWithScale n)) -> FastMult n

{-|
  A type synonym for a fully sequential 'FastMult'. The parameter is supposed to be 'WORD_MAX', but I couldn't find that
  defined, anyway what's important is that anything of scale smaller than @0xFFFFFFFF@ will be sequential, which is everything.
-}
type FastMultSeq = FastMult 0xFFFFFFFF

data BigNatMultResult (n :: Nat) where
  ScaleLT :: BigNatMultResult n
  ScaleEQ :: (KnownNat n) => BigNatWithScale n -> BigNatMultResult n
  ScaleGT :: BigNatMultResult n

singletonStrictList :: a -> Strict.List a
singletonStrictList x = x :! Strict.Nil

instance KnownNat n => Eq (FastMult n) where
  x == y = toInteger x == toInteger y

instance KnownNat n => Ord (FastMult n) where
  x `compare` y = toInteger x `compare` toInteger y

instance KnownNat n => Enum (FastMult n) where
  toEnum = fromIntegral
  fromEnum = fromIntegral

instance KnownNat n => Num (FastMult n) where
  fromInteger = \case
    (S# prim_i) -> case (prim_i >=# 0#) of
      1# -> FastMult Pos (W# (int2Word# prim_i)) Strict.Nil
      0# -> FastMult Neg (W# (int2Word# (negateInt# prim_i))) Strict.Nil
    (Jp# x) -> fromBigNat Pos x
    (Jn# x) -> fromBigNat Neg x
    where
      fromBigNat :: Sign -> BigNat -> FastMult n
      fromBigNat sign x = case (W# (int2Word# (sizeofBigNat# x)) - 1) of
        0 -> FastMult sign (W# (bigNatToWord x)) Strict.Nil
        size -> FastMult sign 1 (singletonStrictList (BigNatWithScale (logBase2Int size) x))
      logBase2Int :: Word -> Word
      logBase2Int x = WORD_SIZE_IN_BITS - 1 - (fromIntegral (countLeadingZeros x))
  (FastMult sign1 w1 l1) * (FastMult sign2 w2 l2) =
    let
      multBigNatWithScale :: forall n. BigNatWithScale n -> BigNatWithScale n -> BigNatMultResult n
      multBigNatWithScale (BigNatWithScale scale1 n1) (BigNatWithScale scale2 n2) =
          case (scale1 `compare` scale2) of
            EQ -> result `seqOrPar` (ScaleEQ (BigNatWithScale (scale1 + 1) result)) where
              result = n1 `timesBigNat` n2
              seqOrPar = if scale1 <= maxSeq then seq else par
            LT -> ScaleLT
            GT -> ScaleGT
          where
            maxSeq = fromIntegral (natVal (undefined :: Proxy n))
      signr = multSigns sign1 sign2
      (# wu_prim, wl_prim #) =
        let
          !(W# w1_prim) = w1
          !(W# w2_prim) = w2
        in
          timesWord2# w1_prim w2_prim
      merge :: Strict.List (BigNatWithScale n) -> Strict.List (BigNatWithScale n) -> Strict.List (BigNatWithScale n)
      merge xl Strict.Nil = xl
      merge Strict.Nil yl = yl
      merge xl@(x:!xs) yl@(y:!ys) = case multBigNatWithScale x y of
        ScaleEQ result -> mergeWithCarry result xs ys
        ScaleLT -> x :! merge xs yl
        ScaleGT -> y :! merge xl ys

      mergeWithCarry :: BigNatWithScale n -> Strict.List (BigNatWithScale n) -> Strict.List (BigNatWithScale n) -> Strict.List (BigNatWithScale n)
      mergeWithCarry carry xl Strict.Nil = mergeOneCarry carry xl
      mergeWithCarry carry Strict.Nil yl = mergeOneCarry carry yl
      mergeWithCarry carry xl@(x:!xs) yl@(y:!ys) = case multBigNatWithScale x y of
        ScaleEQ result -> mergeWithCarry carry xs ys
        ScaleLT -> contCarry x xs yl
        ScaleGT -> contCarry y ys xl
        where
          contCarry x xs yl =
            case multBigNatWithScale carry x of
              ScaleEQ result -> mergeWithCarry result xs yl
              ScaleLT -> carry :! x :! merge xs yl
              ScaleGT -> error $
                "Carry should never be larger than first element. This should never happen. Report as bug.\n" ++
                "Details:\n" ++
                "carry =\n" ++
                show carry ++ "\n" ++
                "xl =\n" ++
                show xl ++ "\n" ++
                "yl =\n" ++
                show yl ++ "\n"

      mergeOneCarry carry Strict.Nil = singletonStrictList carry
      mergeOneCarry carry xl@(x:!xs) = case multBigNatWithScale carry x of
        ScaleLT -> carry :! xl
        ScaleEQ result -> mergeOneCarry result xs
        ScaleGT -> error $
          "Carry should never be larger than first element. This should never happen. Report as bug.\n" ++
          "Details:\n" ++
          "carry =\n" ++
          show carry ++ "\n" ++
          "xl =\n" ++
          show xl ++ "\n"
    in
      case eqWord# wu_prim (int2Word# 0#) of
        0# -> FastMult signr (W# wl_prim) (merge l1 l2)
        _  -> FastMult signr 1 (mergeWithCarry (BigNatWithScale 0 (wordToBigNat2 wu_prim wl_prim)) l1 l2)
  (+) = binaryViaInteger (+)
  (-) = binaryViaInteger (-)
  abs (FastMult _ word l) = FastMult Pos word l
  signum (FastMult Pos _ _) = FastMult Pos 1 Strict.Nil
  signum (FastMult Neg _ _) = FastMult Neg 1 Strict.Nil
  negate (FastMult sign word l) = FastMult (negateSign sign) word l

binaryViaInteger f x y = fromInteger (toInteger x `f` toInteger y)
unaryViaInteger f = fromInteger . f . toInteger

instance KnownNat n => Real (FastMult n) where
  toRational x = (toInteger x) % 1

instance KnownNat n => Integral (FastMult n) where
  toInteger (FastMult sign (W# word_prim) l) = case sign of
    Pos -> Jp# result
    Neg -> Jn# result
    where
      result = foldl' (\x y -> x `timesBigNat` getBigNat y) (wordToBigNat word_prim) l
  x `quotRem` y = let (x_r, y_r) = (toInteger x `quotRem` toInteger y) in (fromInteger x_r, fromInteger y_r)

instance KnownNat n => Show (FastMult n) where
  show = show . toInteger

instance KnownNat n => Read (FastMult n) where
  readsPrec p s = map (\(x,y) -> (fromInteger x,y)) (readsPrec p s)

{-|
  'simplify' returns a 'FastMult' the same as it's argument but "simplified".

  To explain this, consider the following for @x :: FastMult@:

  @
  f x = (show x, x + 1)
  @

  It will multiply out @x@ twice, once for the addition, and once for 'show'. Note that the list of 'BigInt's in @x@ is generally
  a small number, as only one 'BigInt' is stored for each scale, and the sizes of scales increase exponentially, but there
  may be some multiplications required nevertheless. A better way to write this is as follows:

  @
  f x = let y = simplify x in (show y, y + 1)
  @

  This will ensure that @x@ is multiplied out only once.

  Unfortunately using 'simplify' stops your algorithms from being generic,
  so it might be better to define simplify as 'id' with a rewrite rule. I'll think about this.
-}
simplify :: KnownNat n => FastMult n -> FastMult n
simplify = fromInteger . toInteger
