{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}

module GenFuncs where

import qualified Data.Set  as S
import           Data.Void
import           GHC.Exts (Constraint)
import           Prelude   hiding ((*), (+))
import qualified Prelude   as P

infixl 6 +
infixl 7 *

class TSemiring s where
  type C s a :: Constraint
  type C s a = ()

  zero :: s Void
  (+)  :: (C s a, C s b) => s a -> s b -> s (Either a b)
  one  :: s ()
  (*)  :: (C s a, C s b) => s a -> s b -> s (a,b)

class TSemiring s => X s where
  x :: a -> s a

newtype K a b = K a
  deriving Show

liftK :: (a -> b) -> K a x -> K b y
liftK f (K a) = K (f a)

liftK2 :: (a -> b -> c) -> K a x -> K b y -> K c z
liftK2 f (K a) (K b) = K (f a b)

type Semiring a = TSemiring (K a)

instance TSemiring (K Integer) where
  zero = K 0
  one  = K 1
  (+)  = liftK2 (P.+)
  (*)  = liftK2 (P.*)

instance X (K Integer) where
  x _ = K 1

instance TSemiring [] where
  zero    = []
  l1 + l2 = map Left l1 ++ map Right l2
  one     = [()]
  l1 * l2 = [(a,b) | a <- l1, b <- l2]

instance X [] where
  x a = [a]
  -- Maybe this should have the law that  x () = one?

instance TSemiring S.Set where
  type C S.Set a = Ord a

  zero    = S.empty
  s1 + s2 = S.map Left s1 `S.union` S.map Right s2
  one     = S.singleton ()
  s1 * s2 = undefined s1 s2  -- etc.

data GF k a = K k a :> GF k a
  deriving (Show)

zipWithGF :: (Semiring k, C (K k) a, C (K k) b) => GF k a -> GF k b -> GF k (Either a b)
zipWithGF (k1 :> g1) (k2 :> g2) = (k1 + k2) :> zipWithGF g1 g2

instance Semiring k => TSemiring (GF k) where
  zero = zero :> zero
  (+)  = zipWithGF

-- instance (Semiring a, Eq a, HasLub a) => Semiring [a] where
--   zero = []
--   one  = [one]
--   (+) = zipWithExtend (+)

--   -- Have to be careful here since the multiplication in the underlying
--   -- semiring may not be commutative.
--   as * bs = lub (prodGF' id as bs) (prodGF' swap bs as)

-- instance (Eq a, HasLub a, X a) => X [a] where
--   x = zero : x : []

-- zipWithExtend :: (a -> a -> a) -> [a] -> [a] -> [a]
-- -- zipWithExtend _ [] bs = bs
-- -- zipWithExtend _ as [] = as
-- zipWithExtend f ~(a:as) ~(b:bs) = f a b : zipWithExtend f as bs

-- prodGF' :: (Semiring a, HasLub a, Eq a) => ((a,a) -> (a,a)) -> [a] -> [a] -> [a]
-- prodGF' _  []     _       = []
-- prodGF' sw (a:as) ~(b:bs) = (a ^*^ b) : (map (a^*^) bs + (prodGF' sw as (b:bs)))
--   where (^*^) = curry (uncurry (*) . sw)

-- {-

-- >>> let gf = one + (x * gf) :: [Integer]
-- >>> take 5 gf
-- ^CInterrupted.

-- As far as I understand, the above ought to print [1,1,1,1,1].

-- -}
