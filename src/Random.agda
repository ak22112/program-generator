{-# OPTIONS --cubical-compatible --sized-types #-}


module Random where


-- https://agda.readthedocs.io/en/stable/language/instance-arguments.html

open import Data.Nat.PseudoRandom.LCG using ( glibc )
open import Data.Nat.Base as ℕ using ( ℕ;  zero; suc; NonZero )
open import Data.List.Base as List using ( List; []; _∷_ )

open import Data.Nat.PseudoRandom.LCG.Unsafe
open import Codata.Sized.Stream as Stream using ( Stream; take; lookup; map; head; tail )
open import Data.Vec.Base using ( Vec; _∷_; [] )
open import Function.Base using ( _∘_ )

open import Range using ( Range; clamp )

private
  factorial : (n : ℕ) → ℕ
  factorial zero    = 1
  factorial (suc n) = (suc n) ℕ.* factorial n


randoms<n : (n : ℕ) .{{_ : NonZero n}} → Stream ℕ _
randoms<n n = map (Range.val ∘ λ x → clamp 0 n x) (stream glibc 0)

-- example recursive function
-- num is the recursion variable
-- i is a state variable to track which element of the stream is being accessed
ex : (num i : ℕ) → List ℕ
ex zero      i = []
ex (suc num) i = (lookup (randoms<n 10) i) ∷ ex num (suc i)


-- functionally equivalent to ex, but iterating by using the head of the list
-- and passing in the tail when recursing
ex2 : (num : ℕ) → Stream ℕ _ → List ℕ
ex2 zero      stream = []
ex2 (suc num) stream = rand ∷ ex2 num rest
  where
  rand = head stream
  rest = tail stream


private
  safe-take : (num max : ℕ) .{{_ : NonZero max}} → Vec ℕ num
  safe-take num max = take num (randoms<n max)


  -- example recursive function to pull from stream 1 element at a time
  sum : (counter : ℕ) → ℕ
  sum zero          = zero
  sum (suc counter) = lookup (randoms<n 10) counter ℕ.+ sum counter



