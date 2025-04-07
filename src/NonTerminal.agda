module NonTerminal where

open import Agda.Builtin.String using ( String )
open import Relation.Nullary

import Data.String.Properties as StrP

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

-----------------------------------------------------------------
-- NonTerminal type

record NonTerminal : Set where

  constructor nonTerm
  field
    name : String

open NonTerminal

-----------------------------------------------------------------
-- Decidable Equality

_≟_ : (x y : NonTerminal) → Dec (x ≡ y)
(nonTerm name₁) ≟ (nonTerm name₂) with name₁ StrP.≟ name₂
...                                  | yes refl = yes refl
...                                  | no  ¬p   = no (λ q → ¬p (cong name q))
