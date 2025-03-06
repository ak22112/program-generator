module Random where

-- https://agda.readthedocs.io/en/stable/language/instance-arguments.html

open import Data.Nat.PseudoRandom.LCG
open import Data.Nat.Base using ( ℕ; _%_; _+_; _∸_; NonZero )
open import Data.List.Base using ( List; []; _∷_; map )

record Rand : Set where

  constructor rand
  field size : ℕ
  field seed : ℕ
  field min  : ℕ
  field max  : ℕ


open Rand


-- generate a list of random numbers in range [min, max]
randomList : (r : Rand) ⦃ _ : NonZero ((r .max) ∸ (r .min)) ⦄ → List ℕ
randomList r = map (toRange (r .min) (r .max)) (list (r .size) glibc (r .seed))
  where
  -- map LCG output to range [min, max] ensuring (min ∸ max) ≠ 0 (cannot divide by 0)
  toRange : (min max : ℕ) ⦃ _ : NonZero (max ∸ min) ⦄ → ℕ → ℕ
  toRange min max x = (x % (max ∸ min)) + min



private
  -- example: Generate 5 random numbers in range [5, 15] with seed 42
  example : List ℕ
  example = randomList (rand 10 42 1 500)
