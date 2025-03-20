module NonTerminal where

open import Agda.Builtin.String using ( String )
open import Relation.Nullary
open import Data.String.Properties using ( _≟_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

-----------------------------------------------------------------
-- NonTerminal type

record NonTerminal : Set where

  constructor nonTerm
  field
    name : String

-----------------------------------------------------------------
-- Decidable Equality

≟-non-terminal : (x y : NonTerminal) → Dec (x ≡ y)
≟-non-terminal (nonTerm name₁) (nonTerm name₂) with name₁ ≟ name₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (cong NonTerminal.name q))
