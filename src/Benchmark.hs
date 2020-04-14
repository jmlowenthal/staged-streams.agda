{-# LANGUAGE CPP #-}

import Data.Stream

hundredM :: [Num]
hundredM = [x % 10 | x <- 1...100000000]

#if BENCHMARK_sum
main = foldl _+_ 0 HundredM
#endif

-- sumOfSquares : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
-- sumOfSquares r arr =
--   r ← fold _+_ ⟪ + 0 ⟫
--     (ofArr arr
--       ▹ map (λ a → a * a))

-- sumOfSquaresEven : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
-- sumOfSquaresEven r arr =
--   r ← fold _+_ ⟪ + 0 ⟫
--     (ofArr arr
--       ▹ filter (λ e → (e % ⟪ + 2 ⟫) == ⟪ + 0 ⟫)
--       ▹ map (λ a → a * a))

-- -- Sum over Cartesian-/outer-product
-- cart : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
-- cart r x y =
--   r ← fold _+_ ⟪ + 0 ⟫
--   (ofArr x
--     ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

-- maps : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
-- maps r arr =
--   iter (λ e → r ≔ e)
--     (ofArr arr
--       ▹ map (λ e → e * ⟪ + 2 ⟫)
--       ▹ map (λ e → e * ⟪ + 3 ⟫))

-- filters : ∀ { n } → Ref Int → Ref (Array Int n) → Statement
-- filters r arr =
--   iter (λ e → r ≔ e)
--     (ofArr arr
--       ▹ filter (λ e → ! (e == ⟪ + 5 ⟫))
--       ▹ filter (λ e → ! (e == ⟪ + 10 ⟫)))

-- dotProduct : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
-- dotProduct r x y =
--   r ← fold _+_ ⟪ + 0 ⟫
--     (zipWith (λ i j → i * j) (ofArr x) (ofArr y) {ℕ.z≤n})

-- flatmap-after-zipWith : ∀ { n m } → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
-- flatmap-after-zipWith r x y =
--   iter (λ e → r ≔ e)
--     (zipWith _+_ (ofArr x) (ofArr x) {ℕ.z≤n}
--       ▹ flatmap (λ i → ofArr y ▹ map (λ j → i * j)))

-- zipWith-after-flatmap : ∀ { n } → Ref Int → Ref (Array Int (n ℕ.* n)) → Ref (Array Int n) → Statement
-- zipWith-after-flatmap r x y =
--   iter (λ e → r ≔ e)
--     (zipWith _+_
--     (ofArr x)
--     (flatmap (λ e → ofArr y ▹ map (λ a → a + e)) (ofArr y))
--     {ℕ.s≤s ℕ.z≤n})

-- flatmap-take : ∀ { n m } → ℕ → Ref Int → Ref (Array Int n) → Ref (Array Int m) → Statement
-- flatmap-take i r x y =
--   iter (λ e → r ≔ e)
--     (ofArr x
--       ▹ flatmap (λ a → ofArr y ▹ map (λ b → a + b))
--       ▹ take ⟪ + i ⟫)
