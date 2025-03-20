module Rule where

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )
open import Data.List using ( List )

open import NonTerminal using ( NonTerminal; ≟-non-terminal )
open import Symbol using ( Symbol; ≟-list-symbol )

-----------------------------------------------------
-- Rule type

record Rule : Set where

  constructor rule
  field
    lhs : NonTerminal
    rhs : List Symbol

-----------------------------------------------------
-- Decidable Equality

≟-rule : (r₁ r₂ : Rule) → Dec (r₁ ≡ r₂)
≟-rule (rule lhs₁ rhs₁) (rule lhs₂ rhs₂)
  with ≟-non-terminal lhs₁ lhs₂ | ≟-list-symbol rhs₁ rhs₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ q → ¬p (cong Rule.lhs q))
... | _        | no ¬q    = no (λ q → ¬q (cong Rule.rhs q))
