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



open import Data.List using ( List; _∷_; []; _++_ )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( here; there )


_ : 2 ∈ 0 ∷ 2 ∷ []
_ = there (here refl)


open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)






-- decidable equality for natural numbers (required to find proof of list membership for natural numbers)
decEqNat : (x y : Nat) → Dec (x ≡ y)
decEqNat zero    zero    = yes refl
decEqNat zero    (suc y) = no (λ ())
decEqNat (suc x) zero    = no (λ ())
decEqNat (suc x) (suc y) with decEqNat x y
... | yes p = yes (cong suc p)
... | no ¬p = no  (λ q → ¬p (suc-injective q))
  where
  suc-injective : ∀ {x y : Nat} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl



-- This is the general form for a proof finder for list membership
-- As long as you define DECIDABLE EQUALITY for A, this will work
findProof : {A : Set} → (decEq : ∀ (x y : A) → Dec (x ≡ y)) 
         → (x : A) → (xs : List A) → Maybe (x ∈ xs)
findProof decEq x []       = nothing
findProof decEq x (y ∷ xs) with decEq x y
... | yes refl = just (here refl)                  -- x ≡ y     →  so `here refl`
... | no  _    = map there (findProof decEq x xs)  -- otherwise → `there` then recurse


-- special case for natural numbers specifically
findProofNat : (x : Nat) (xs : List Nat) → Maybe (x ∈ xs)
findProofNat x xs = findProof decEqNat x xs



-- examples

p₁ : Maybe (2 ∈ (0 ∷ 1 ∷ 2 ∷ []))
p₁ = findProof decEqNat 2 (0 ∷ 1 ∷ 2 ∷ [])


p₂ : Maybe (2 ∈ (1 ∷ 2 ∷ 3 ∷ []))
p₂ = findProofNat 2 (1 ∷ 2 ∷ 3 ∷ [])
-- c-c c-n p₂ → just (there (here refl))


p₃ : Maybe (5 ∈ (1 ∷ 2 ∷ 3 ∷ []))
p₃ = findProofNat 5 (1 ∷ 2 ∷ 3 ∷ [])
-- c-c c-n p₃ → nothing
