{-# OPTIONS --cubical-compatible --sized-types #-}


module Random where


-- https://agda.readthedocs.io/en/stable/language/instance-arguments.html

open import Data.Nat.PseudoRandom.LCG
open import Data.Nat.Base using ( ℕ; _%_; _+_; _∸_; _<_; _≤_; s≤s; z≤n; suc; zero; _*_; NonZero )
open import Data.List.Base as List using ( List; []; _∷_ )
open import Data.Nat.DivMod


record Rand : Set where

  constructor rand
  field size : ℕ
  field seed : ℕ
  field min  : ℕ
  field max  : ℕ


open Rand
open Generator


-- generate a list of random numbers in range [min, max)
randomList : (r : Rand) ⦃ _ : NonZero ((r .max) ∸ (r .min)) ⦄ → List ℕ
randomList r = List.map (toRange (r .min) (r .max)) (list (r .size) glibc (r .seed))
  where
  -- map LCG output to range [min, max) ensuring (min ∸ max) ≠ 0 (cannot divide by 0)
  toRange : (min max : ℕ) ⦃ _ : NonZero (max ∸ min) ⦄ → ℕ → ℕ
  toRange min max x = (x % (max ∸ min)) + min


private
  -- example: Generate 10 random numbers in range [1, 500) with seed 42
  example : List ℕ
  example = randomList (rand 10 42 1 500)



open import Data.Nat.PseudoRandom.LCG.Unsafe
open import Codata.Sized.Stream as Stream using ( Stream; take; lookup; map )
open import Data.Vec.Base using ( Vec; _∷_; [])
open import Function.Base using ( _∘_ )


open import Range using ( Range; clamp )

private
  factorial : (n : ℕ) → ℕ
  factorial zero    = 1
  factorial (suc n) = (suc n) * factorial n


randoms<n : (n : ℕ) .{{_ : NonZero n}} → Stream ℕ _
randoms<n n = map (Range.val ∘ λ x → clamp 0 n x) (stream glibc 0)

-- example recursive function
-- num is the recursion variable
-- i is a state variable to track which element of the stream is being accessed
ex : (num i : ℕ) → List ℕ
ex zero      i = []
ex (suc num) i = (lookup (randoms<n 10) i) ∷ ex num (suc i)


private
  safe-take : (num max : ℕ) .{{_ : NonZero max}} → Vec ℕ num
  safe-take num max = take num (randoms<n max)


  -- example recursive function to pull from stream 1 element at a time
  sum : (counter : ℕ) → ℕ
  sum zero          = zero
  sum (suc counter) = lookup (randoms<n 10) counter + sum counter



