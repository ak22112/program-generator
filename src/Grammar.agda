module Grammar where

open import Data.List using ( List; filter )
open import NonTerminal using ( NonTerminal; ≟-non-terminal )
open import Rule

-------------------------------------------------------------
-- Grammar type


record Grammar : Set where

  constructor grammar
  field
    rules : List Rule

-------------------------------------------------------------
-- open records to make dot notation accessible

open Rule.Rule
open Grammar

-------------------------------------------------------------
-- Filter a grammar by non-terminal

-- filter Grammar by non-terminal
-- see list filtering functions here https://agda.github.io/agda-stdlib/v2.1/Data.List.Base.html
filterGrammar : (g : Grammar) (x : NonTerminal) → Grammar
filterGrammar g x = grammar (filter (λ r → ≟-non-terminal (r .lhs) x) (g .rules))
