module Terminal where

open import Agda.Builtin.String using ( String )
open import Relation.Nullary
import Data.String.Properties as StrP
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

----------------------------------------------------------
-- Terminal type

record Terminal : Set where

  constructor term
  field
    name : String

open Terminal

----------------------------------------------------------
-- Decidable Equality

_≟_ : (x y : Terminal) → Dec (x ≡ y)
(term name₁) ≟ (term name₂) with name₁ StrP.≟ name₂
...                            | yes refl = yes refl
...                            | no  ¬p   = no (λ q → ¬p (cong name q))
