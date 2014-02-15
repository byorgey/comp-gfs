{-# LANGUAGE DeriveFunctor #-}
module GenFuncs where

import           Data.Lub
import           Data.Tuple (swap)
import           Data.Unamb
import           Prelude    hiding ((*), (+))
import qualified Prelude    as P

infixl 6 +
infixl 7 *

class Semiring a where
  zero :: a
  one  :: a
  (+)  :: a -> a -> a
  (*)  :: a -> a -> a

class Semiring a => X a where
  x :: a

instance Semiring Integer where
  zero  = 0
  one   = 1
  (+) = parIdentity (P.+) 0
  (*) = parAnnihilatorIdentity (P.*) 0 1

instance X Integer where
  x = 1

instance (Eq a, HasLub a, X a) => X [a] where
  x = zero : x : []

instance (Semiring a, Eq a, HasLub a) => Semiring [a] where
  zero = []
  one  = [one]
  (+) = zipWithExtend (+)

  -- Have to be careful here since the multiplication in the underlying
  -- semiring may not be commutative.
  as * bs = lub (prodGF' id as bs) (prodGF' swap bs as)

zipWithExtend :: (a -> a -> a) -> [a] -> [a] -> [a]
-- zipWithExtend _ [] bs = bs
-- zipWithExtend _ as [] = as
zipWithExtend f ~(a:as) ~(b:bs) = f a b : zipWithExtend f as bs

prodGF' :: (Semiring a, HasLub a, Eq a) => ((a,a) -> (a,a)) -> [a] -> [a] -> [a]
prodGF' _  []     _       = []
prodGF' sw (a:as) ~(b:bs) = (a ^*^ b) : (map (a^*^) bs + (prodGF' sw as (b:bs)))
  where (^*^) = curry (uncurry (*) . sw)

{-

>>> let gf = one + (x * gf) :: [Integer]
>>> take 5 gf
^CInterrupted.

As far as I understand, the above ought to print [1,1,1,1,1].

-}
