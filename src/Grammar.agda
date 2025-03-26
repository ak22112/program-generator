module Grammar where

open import Data.Nat.Base using ( ℕ )
open import Data.List using ( List; filter; _∷_; []; lookup; length )
open import Data.Fin using ( Fin; toℕ; fromℕ; zero; suc )
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
-- Filter a grammar by non-terminal

-- filter Grammar by non-terminal
-- see list filtering functions here https://agda.github.io/agda-stdlib/v2.1/Data.List.Base.html
filterGrammar : (g : Grammar) (x : NonTerminal) → Grammar
filterGrammar g x = grammar (filter (λ r → ≟-non-terminal (r .lhs) x) (g .rules))


-- temporary testing examples
xs : List ℕ
--   0   1   2
xs = 4 ∷ 9 ∷ 2 ∷ []

i : Fin (length xs)
i = suc zero

xs[i] : ℕ
xs[i] = lookup xs i


-- pick the ith rule in a grammar
lookup-rule : (g : Grammar) → Fin (length (g .rules)) → Rule
lookup-rule g i = lookup (g .rules) i

