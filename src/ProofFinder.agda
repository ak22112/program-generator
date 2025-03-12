module ProofFinder where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Data.Maybe.Base

data Even : Nat → Set where
  even0   : Even 0                              -- 0 is even
  even+2  : ∀ {n} → Even n → Even (suc (suc n)) -- even + 2 is also even


evenProof : (n : Nat) → Maybe (Even n)
evenProof 0       = just even0
evenProof (suc 0) = nothing
evenProof (suc (suc n)) with evenProof n
... | just x = just (even+2 x)
... | nothing = nothing



-- benefit of using a proof finder is that `refl` is now always a sufficient proof
-- this means it is easier to use in other functions

_ : evenProof 4 ≡ just (even+2 (even+2 even0))
_ = refl


_ : evenProof 3 ≡ nothing
_ = refl
