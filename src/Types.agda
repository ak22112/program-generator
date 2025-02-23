module Types where

open import Agda.Builtin.List
open import Agda.Builtin.String


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
