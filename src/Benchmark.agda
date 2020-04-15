open import C.Base
open import C.Extras
open import Data.Integer as ℤ using (+_)
open import Data.List as List using (List ; _∷_ ; [])
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.String as String using (String ; _++_)
open import Data.Vec as Vec using (Vec ; _∷_ ; [])
open import IO
open import Print.Print
open import Streams

import Data.Nat.Show as ℕs
import Data.Fin as Fin
import Data.Nat.DivMod as ℕ÷

module Benchmark where

record CWithPrintf : Set₁ where
  field
    ⦃ ℐ ⦄ : C
    printInt : C.Expr ℐ Int → C.Statement ℐ

open C ⦃ ... ⦄
open CWithPrintf ⦃ ... ⦄

-- Kiselyov et al., Section §7:
--
-- - sum: the simplest of_arr arr ▹ sum pipeline, summing the elements of an array;
-- - sumOfSquares: our running example from §4.2 on;
-- - sumOfSquaresEven: the sumOfSquares benchmark with added filter, summing the squares of only the even array elements;
-- - cart: ∑ xᵢ yⱼ, using flat_map to build the outer-product stream;
-- - maps: consecutive map operations with integer multiplication;
-- - filters: consecutive filter operations using integer comparison;
-- - dotProduct: compute dot product of two arrays using zip_with;
-- - flatMapafterzipWith: compute ∑ (xᵢ+xᵢ) yⱼ, like cart above, doubling the x array via zip_with (+) with itself;
-- - zipWithafterflatMap: zip_with of two streams one of whichis the result of flat_map;
-- - flatmaptake: flat_map followed by take"
--
-- Input: All tests were run with the same input set. For the sum, sumOfSquares, sumOfSquaresEven, maps, filters we used an array of N = 100,000,000 small integers: xᵢ = i mod 10. The cart test iterates over two arrays. An outer one of 10,000,000 integers and an inner one of 10. For the dotProduct we used 10,000,000 integers, for the flatMap_after_zipWith 10,000, for the zipWith_after_flatMap 10,000,000 and for the flatmap_take N numbers sub-sized by 20% of N."

module Tests ⦃ _ : CWithPrintf ⦄ where


  gen : ℕ → Stream Int
  gen n = nat n ▹ map (λ e → e % ⟪ + 10 ⟫ - ⟪ + 2 ⟫ * (e % ⟪ + 7 ⟫))

  100M = gen 100000000
  10M =  gen  10000000
  10K =  gen     10000

  sum : Statement
  sum =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫ 100M ；
    printInt (★ r)

  sumOfSquares : Statement
  sumOfSquares =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (100M ▹ map (λ a → a * a)) ；
    printInt (★ r)

  sumOfSquaresEven : Statement
  sumOfSquaresEven =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (100M
        ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
        ▹ map (λ a → a * a)) ；
    printInt (★ r)

  -- Sum over Cartesian-/outer-product
  cart : Statement
  cart =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (10M ▹ flatmap (λ i → 10M ▹ map (λ j → i * j))) ；
    printInt (★ r)

  maps : Statement
  maps =
    iter (λ e → printInt e)
      (100M
        ▹ map (λ e → e * ⟪ + 2 ⟫)
        ▹ map (λ e → e * ⟪ + 3 ⟫))

  filters : Statement
  filters =
    iter (λ e → printInt e)
      (100M
        ▹ filter (λ e → ! ((e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫))
        ▹ filter (λ e → ! ((e % ⟪ + 8 ⟫) == ⟪ + 0 ⟫)))

  dotProduct : Statement
  dotProduct =
    decl Int λ r →
    r ← fold _+_ ⟪ + 0 ⟫
      (zipWith (λ i j → i * j) 10M 10M {ℕ.z≤n}) ；
    printInt (★ r)

  flatmap-after-zipWith : Statement
  flatmap-after-zipWith =
    iter (λ e → printInt e)
      (zipWith _+_ 10K 10K {ℕ.z≤n}
        ▹ flatmap (λ i → 10K ▹ map (λ j → i * j)))

  zipWith-after-flatmap : Statement
  zipWith-after-flatmap =
    iter (λ e → printInt e)
      (zipWith _+_ 100M (flatmap (λ e → 10K ▹ map (λ a → a + e)) 10K) {ℕ.s≤s ℕ.z≤n})

  flatmap-take : Statement
  flatmap-take =
    iter (λ e → printInt e)
      (10K
        ▹ flatmap (λ a → 10K ▹ map (λ b → a + b))
        ▹ take ⟪ + 20000000 ⟫)

AST-CWithPrintf : CWithPrintf
CWithPrintf.ℐ AST-CWithPrintf = Print-C
CWithPrintf.printInt AST-CWithPrintf e n = n , "printf(\"%d\\n\", " ++ e ++ ");\n"

benchmark-function : String → (∀ ⦃ _ : CWithPrintf ⦄ → Statement) → String
benchmark-function name body =
  "#if BENCHMARK_" ++ name ++ "\n"
  ++ "int main(void){\n"
    ++ proj₂ (body ⦃ AST-CWithPrintf ⦄ 0)
    ++ "return 0;\n"
  ++ "}\n"
  ++ "#endif\n\n"

main =
  run (IO.putStr ex)
  where
    ex : String
    ex =
      "#include <stdio.h>\n"
      ++ "#include <stdlib.h>\n"
      ++ (benchmark-function "sum" Tests.sum)
      ++ (benchmark-function "sumOfSquares" Tests.sumOfSquares)
      ++ (benchmark-function "sumOfSquaresEven" Tests.sumOfSquaresEven)
      ++ (benchmark-function "cart" Tests.cart)
      ++ (benchmark-function "maps" Tests.maps)
      ++ (benchmark-function "filters" Tests.filters)
      ++ (benchmark-function "dotProduct" Tests.dotProduct)
      ++ (benchmark-function "flatmap_after_zipWith" Tests.flatmap-after-zipWith)
      ++ (benchmark-function "zipWith_after_flatmap" Tests.zipWith-after-flatmap)
      ++ (benchmark-function "flatmap_take" Tests.flatmap-take)
