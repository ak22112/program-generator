module Rule where

open import Agda.Builtin.List using ( List )

open import NonTerminal using ( NonTerminal )
open import Symbol using ( Symbol )


record Rule : Set where

  constructor rule
  field
    lhs : NonTerminal
    rhs : List Symbol
