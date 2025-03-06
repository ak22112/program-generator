module Random where

open import Data.Nat.PseudoRandom.LCG


open import Data.Nat.Base using ( ℕ; _%_; _+_; _∸_; NonZero )
open import Data.List.Base using ( List; []; _∷_; map )

-- Map LCG output to range [1, n] ensuring n ≠ 0
toRange : (min max : ℕ) ⦃ _ : NonZero (max ∸ min) ⦄ → ℕ → ℕ
toRange min max x = (x % (max ∸ min)) + min

-- Generate a list of random numbers in range [min, max]
randomList : (size seed min max : ℕ) ⦃ _ : NonZero (max ∸ min) ⦄ → List ℕ
randomList size seed min max = map (toRange min max) (list size glibc seed)

-- Example: Generate 5 random numbers in range [5, 15] with seed 42
example : List ℕ
example = randomList 20 42 5 10

