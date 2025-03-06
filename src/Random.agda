module Random where

open import Data.Nat.PseudoRandom.LCG


open import Data.Nat.Base using ( ℕ; _%_; _+_ )
open import Data.List.Base using ( List; []; _∷_; map )

-- Map LCG output to range [1, 10]
toRange : ℕ → ℕ
toRange x = (x % 10) + 1

-- Generate a list of n random numbers in range [1, 10]
randomList : ℕ → ℕ → List ℕ
randomList n seed = map toRange (list n glibc seed)

-- Example: Generate 5 random numbers with seed 42
example : List ℕ
example = randomList 5 42
