{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NumericUnderscores #-}

import Data.Stream
import GHC.Num
import GHC.Int
import Data.Function ((&))
import Prelude (mod, print, (==), not)

gen :: Int -> Stream Int
gen n = stream [x `mod` 10 | x <- [1..n]]

hundredM = gen 100_000_000
tenM = gen 10_000_000
tenK = gen 10_000
ten = gen 10

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
main = print (
  hundredM
    & map (\e -> e * 2)
    & map (\e -> e * 3)
    & foldr (\x y -> y) 0)
#endif

#if BENCHMARK_filters
main = print (
  hundredM
    & filter (\e -> not (e `mod` 5 == 0))
    & filter (\e -> not (e `mod` 8 == 0))
    & foldr (\x y -> y) 0)
#endif

#if BENCHMARK_dotProduct
main = print (
  zipWith (\i j -> i * j) tenM tenM
    & foldr (\x y -> y) 0)
#endif

#if BENCHMARK_flatmap_after_zipWith
main = print (
  zipWith (+) tenK tenK
    & concatMap (\i -> tenK & map (\j -> i * j))
    & foldr (\x y -> y) 0)
#endif

#if BENCHMARK_zipWith_after_flatmap
main = print (
  zipWith (+) hundredM (concatMap (\e -> tenK & map (\a -> a + e)) tenK)
    & foldr (\x y -> y) 0)
#endif

#if BENCHMARK_flatmap_take
main = print (
  tenK
    & concatMap (\a -> tenK & map (\b -> a + b))
    & take 20000000
    & foldr (\x y -> y) 0)
#endif
