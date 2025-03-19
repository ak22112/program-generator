module Terminal where

open import Agda.Builtin.String using ( String )


record Terminal : Set where

  constructor term
  field
    name : String
