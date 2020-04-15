{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NumericUnderscores #-}

import Data.Stream
import Data.Array
import GHC.Num
import GHC.Int
import Data.Function
import Prelude hiding (foldr, foldl, map, sum)

gen :: Int -> Stream Int
gen n = Stream next (L 0)
  where
    arr = listArray (0, n - 1) [x `mod` 10 | x <- [1..n]]
    next (L i) = if n == i then Done
                 else Yield (arr ! i) (L (i + 1))

hundredM = gen 100_000_000
tenM = gen 10_000_000
tenK = gen 10_000
ten = gen 10

printAll = foldl (\x y -> x >>= \_ -> print y) (putStr "")

#if BENCHMARK_sum
main = print (
  hundredM
    & sum)
#endif

#if BENCHMARK_sumOfSquares
main = print (
  hundredM
    & map (\x -> x * x)
    & sum)
#endif

#if BENCHMARK_sumOfSquaresEven
main = print (
  hundredM
    & filter (\x -> x `mod` 2 == 0)
    & map (\x -> x * x)
    & sum)
#endif

#if BENCHMARK_cart
main = print (
  tenM
    & concatMap (\i -> ten & map (\j -> i * j))
    & sum)
#endif

#if BENCHMARK_maps
main =
  hundredM
    & map (\e -> e * 2)
    & map (\e -> e * 3)
    & printAll
#endif

#if BENCHMARK_filters
main =
  hundredM
    & filter (\e -> not (e `mod` 5 == 0))
    & filter (\e -> not (e `mod` 8 == 0))
    & printAll
#endif

#if BENCHMARK_dotProduct
main =
  zipWith (\i j -> i * j) tenM tenM
    & printAll
#endif

#if BENCHMARK_flatmap_after_zipWith
main =
  zipWith (+) tenK tenK
    & concatMap (\i -> tenK & map (\j -> i * j))
    & printAll
#endif

#if BENCHMARK_zipWith_after_flatmap
main =
  zipWith (+) hundredM (concatMap (\e -> tenK & map (\a -> a + e)) tenK)
    & printAll
#endif

#if BENCHMARK_flatmap_take
main =
  tenK
    & concatMap (\a -> tenK & map (\b -> a + b))
    & take 20000000
    & printAll
#endif
