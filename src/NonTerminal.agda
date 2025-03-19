module NonTerminal where

open import Agda.Builtin.String using ( String )


record NonTerminal : Set where

  constructor nonTerm
  field
    name : String
