module Grammar where

open import Data.Nat.Base using ( ℕ; _<_; zero; suc; z≤n; s≤s )
open import Data.List using ( List; filter; _∷_; []; lookup; length; allFin )
open import Data.Fin using ( Fin; toℕ; fromℕ; fromℕ<; zero; suc )
open import NonTerminal using ( NonTerminal ) renaming ( ≟-non-terminal to _≟_ )
open import Rule
open import Random

-------------------------------------------------------------
-- Grammar type

record Grammar : Set where

  constructor grammar
  field
    rules : List Rule

-------------------------------------------------------------
-- open records to make dot notation accessible

open Rule.Rule
open Random.Rand
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
