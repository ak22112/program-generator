module program-generator.start.Start where

open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Product using (_×_; _,_)


-- terminal symbols
record Terminal : Set where

  constructor term
  field name : String


-- non-terminal symbols
record NonTerminal : Set where

  constructor nonTerm
  field name : String


-- symbols (terminals and non-terminals)
data Symbol : Set where

  T : Terminal    → Symbol
  N : NonTerminal → Symbol


-- production rule
record Rule : Set where

  constructor rule
  field
    lhs : NonTerminal
    rhs : List Symbol


-- grammar (list of production rules)
record Grammar : Set where

  constructor grammar
  field
    rules : List Rule


-- concrete definition of an example grammar
G : Grammar
G = grammar
    (
      rule (nonTerm "X") (T (term "a") ∷ N (nonTerm "X") ∷ []) ∷    -- X → a X
      rule (nonTerm "X") (T (term "b") ∷ N (nonTerm "Y") ∷ []) ∷    -- X → b Y
      rule (nonTerm "X") []                                    ∷    -- X → ϵ
      rule (nonTerm "Y") (T (term "c") ∷ N (nonTerm "Y") ∷ []) ∷    -- Y → c Y
      rule (nonTerm "Y") (T (term "d") ∷ [])                   ∷    -- Y → d
      []
    )
