module Grammar where

open import Agda.Builtin.List using ( List )
open import Rule


record Grammar : Set where

  constructor grammar
  field
    rules : List Rule
