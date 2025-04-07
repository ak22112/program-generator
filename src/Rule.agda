module Rule where

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )
open import Data.List using ( List )

open import NonTerminal using ( NonTerminal )
open import Symbol using ( Symbol )

-----------------------------------------------------
-- Rule type

record Rule : Set where

  constructor rule
  field
    lhs : NonTerminal
    rhs : List Symbol

open Rule

-----------------------------------------------------
-- Decidable Equality

_≟_ : (r₁ r₂ : Rule) → Dec (r₁ ≡ r₂)
(rule lhs₁ rhs₁) ≟ (rule lhs₂ rhs₂)
  with lhs₁ NonTerminal.≟ lhs₂ | rhs₁ Symbol.≟ₗ rhs₂
...                 | yes refl | yes refl = yes refl
...                 | no  ¬p   | _        = no (λ q → ¬p (cong lhs q))
...                 | _        | no  ¬q   = no (λ q → ¬q (cong rhs q))
