module program-generator.start.Start where

open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Product using (_×_; _,_)


-- terminal symbols
data Terminal : Set where

  -- TODO: expand for general grammars
  a b c d : Terminal


-- non-terminal symbols
data NonTerminal : Set where

  -- TODO: expand for general grammars
  X Y : NonTerminal


-- symbols
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
      rule X (T a ∷ N X ∷ []) ∷    -- X → a X
      rule X (T b ∷ N Y ∷ []) ∷    -- X → b Y
      rule X []               ∷    -- X → ϵ
      rule Y (T c ∷ N Y ∷ []) ∷    -- Y → c Y
      rule Y (T d ∷ [])       ∷    -- Y → d
      []
    )
