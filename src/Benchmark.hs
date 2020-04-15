{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NumericUnderscores #-}

import Data.Stream
import Data.Array
import GHC.Num
import GHC.Int
import Data.Function
import Data.Maybe
import Prelude hiding (foldr, foldl, map, sum, filter, concatMap)

nat :: Int -> Stream Int
nat n = unfoldr step 0
  where
    step :: Int -> Maybe (Int, Int)
    step i = if i < n then Just (i, i + 1) else Nothing

gen :: Int -> Stream Int
gen n =
  nat n
    & map (\e -> e `mod` 10 - 2 * (e `mod` 7))

hundredM = gen 100_000_000
tenM = gen 10_000_000
tenK = gen 10_000
ten = gen 10

printAll :: Show a => Stream a -> IO ()
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
main = print (
  zipWith (\i j -> i * j) tenM tenM
    & sum)
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
