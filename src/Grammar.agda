module Grammar where

open import Data.Nat.Base using ( ℕ; _<_; zero; suc; z≤n; s≤s )
open import Data.List using ( List; filter; _∷_; []; lookup; length; allFin )
open import Data.Fin using ( Fin; toℕ; fromℕ; fromℕ<; zero; suc )
open import NonTerminal using ( NonTerminal; ≟-non-terminal )
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

-- temporary testing examples
xs : List ℕ
--   0   1   2
xs = 4 ∷ 9 ∷ 2 ∷ 5 ∷ []

i : Fin (length xs)
i = suc zero

xs[i] : ℕ
xs[i] = lookup xs i


-- pick the ith rule in a grammar
lookup-rule : (g : Grammar) → Fin (length (g .rules)) → Rule
lookup-rule g i = lookup (g .rules) i


-- Filter a grammar by non-terminal

-- filter Grammar by non-terminal
-- see list filtering functions here https://agda.github.io/agda-stdlib/v2.1/Data.List.Base.html
filter-grammar : (g : Grammar) (x : NonTerminal) → Grammar
filter-grammar g x = grammar (filter (λ r → ≟-non-terminal (r .lhs) x) (g .rules))


-- work out which rules satisfy (r .lhs ≡ x), and return a list of indices
-- then pick a random one of these numbers
filter-grammar-index : (g : Grammar) (x : NonTerminal) → List (Fin (length (g .rules)))
filter-grammar-index g x = filter (λ i → ≟-non-terminal ((lookup-rule g i) .lhs) x) (allFin (length (g .rules)))



get-index : {A : Set} (n : ℕ) (ys : List A)
          → n < length ys
          ---------------
          → Fin (length ys)

get-index n ys n<length = fromℕ< n<length

index0 : Fin (length xs)
index0 = get-index 0 xs (s≤s z≤n)

index1 : Fin (length xs)
index1 = get-index 1 xs (s≤s (s≤s z≤n))

index2 : Fin (length xs)
index2 = get-index 2 xs (s≤s (s≤s (s≤s z≤n)))




-- doesn't work
get-index2 : {A : Set} (n : ℕ) (ys : List A) → ⦃ p : n < length ys ⦄ → Fin (length ys)
get-index2 n ys {{p}} = fromℕ< p

-- does not type check
-- index : Fin (length xs)
-- index = get-index2 1 xs
