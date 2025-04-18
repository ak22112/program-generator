{-# OPTIONS --sized-types #-}

module Grammar where

open import Data.Nat.Base using ( ℕ; _<_; zero; suc; z≤n; s≤s; NonZero; _∸_ )
open import Data.List using ( List; filter; _∷_; []; lookup; length; allFin )
open import Data.Fin using ( Fin; toℕ; fromℕ; fromℕ<; zero; suc )
open import NonTerminal using ( NonTerminal; _≟_ )
open import Rule using ( Rule )
open import Random
open import Range

open import Codata.Sized.Stream as Stream using ( Stream; take )
open import Data.Vec.Base using ( Vec; _∷_; [] )

-------------------------------------------------------------
-- Grammar type

record Grammar : Set where

  constructor grammar
  field
    rules : List Rule

-------------------------------------------------------------
-- open records to make dot notation accessible

open Rule.Rule    -- .lhs; .rhs
open Range.Range  -- .val; .min≤val; .val<max

open Grammar

-------------------------------------------------------------
-- Lookup a rule in a grammar

lookup-rule : (g : Grammar) → Fin (length (g .rules)) → Rule
lookup-rule g i = lookup (g .rules) i

-------------------------------------------------------------
-- Filtering (by non-terminal)
-- see list filtering functions here https://agda.github.io/agda-stdlib/v2.1/Data.List.Base.html

-- return a new grammar of elements that satisfy the filter
filter-grammar : (g : Grammar) (x : NonTerminal) → Grammar
filter-grammar g x = grammar (filter (λ r → (r .lhs) ≟ x) (g .rules))

-- return list of indices of elements which satisfy the filter
filter-grammar-index : (g : Grammar) (x : NonTerminal) → List (Fin (length (g .rules)))
filter-grammar-index g x = filter (λ i → ((lookup-rule g i) .lhs) ≟ x) (allFin (length (g .rules)))

-------------------------------------------------------------
-- Convert ℕ to Fin of constant size

get-index : {A : Set} (n : ℕ) (xs : List A)
          → n < length xs
          ---------------
          → Fin (length xs)

get-index n xs n<length = fromℕ< n<length

-- (PoC) use postulate to get around proof (should not be used)
get-indexᵖ : {A : Set} (n : ℕ) (xs : List A) → Fin (length xs)
get-indexᵖ n xs = fromℕ< n<length
  where postulate n<length : n < length xs

get-index-from-range : {A : Set} (xs : List A) .{{_ : NonZero (length xs)}} (r : Range 0 (length xs)) → Fin (length xs)
get-index-from-range xs r = fromℕ< (r .val<max)

ℕtoFin : {A : Set} (n : ℕ) (xs : List A) .{{_ : NonZero (length xs)}} → Fin (length xs)
ℕtoFin n xs = get-index-from-range xs (clamp 0 (length xs) n)

-- need to make sure this function is never called on an empty list
lookup-in-bounds : {A : Set} (xs : List A) (n : ℕ) .{{_ : NonZero (length xs)}} → A
lookup-in-bounds xs n = lookup xs (ℕtoFin n xs)

safe-lookup-rule : (g : Grammar) (n : ℕ) .{{_ : NonZero (length (g .rules))}} → Rule
safe-lookup-rule g n = lookup-in-bounds (g .rules) n

-------------------------------------------------------------
-- Examples

xs : List ℕ
--   0   1   2
xs = 4 ∷ 9 ∷ 2 ∷ 5 ∷ []

i : Fin (length xs)
i = suc zero

xs[i] : ℕ
xs[i] = lookup xs i

index0 : Fin (length xs)
index0 = get-index 0 xs (s≤s z≤n)

index1 : Fin (length xs)
index1 = get-index 1 xs (s≤s (s≤s z≤n))

index2 : Fin (length xs)
index2 = get-index 2 xs (s≤s (s≤s (s≤s z≤n)))

index3 : Fin (length xs)
index3 = get-indexᵖ 3 xs
