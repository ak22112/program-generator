module Terminal where

open import Agda.Builtin.String using ( String )
open import Relation.Nullary
open import Data.String.Properties using ( _≟_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

----------------------------------------------------------
-- Terminal type

record Terminal : Set where

  constructor term
  field
    name : String

----------------------------------------------------------
-- Decidable Equality

≟-terminal : (x y : Terminal) → Dec (x ≡ y)
≟-terminal (term name₁) (term name₂) with name₁ ≟ name₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (cong Terminal.name q))
