module Symbol where

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )
open import Data.List using ( List; _∷_; [] )

open import Terminal using ( Terminal; ≟-terminal )
open import NonTerminal using ( NonTerminal; ≟-non-terminal )

-------------------------------------------------------------
-- Symbol type

data Symbol : Set where

  T : Terminal    → Symbol
  N : NonTerminal → Symbol

-------------------------------------------------------------
-- Decidable Equality


-- Decidable equality for Symbol

≟-symbol : (x y : Symbol) → Dec (x ≡ y)

≟-symbol (T t₁) (T t₂) with ≟-terminal t₁ t₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (inj-terminal q))
  where
  inj-terminal : ∀ {x y : Terminal}
       → T x ≡ T y
       -----------
       → x ≡ y
  inj-terminal refl = refl

≟-symbol (N n₁) (N n₂) with ≟-non-terminal n₁ n₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (inj-nonterminal q))
  where
  inj-nonterminal : ∀ {x y : NonTerminal}
       → N x ≡ N y
       -----------
       → x ≡ y
  inj-nonterminal refl = refl

≟-symbol (T _) (N _) = no (λ ())
≟-symbol (N _) (T _) = no (λ ())


-- Decidable equality for List Symbol

≟-list-symbol : (xs ys : List Symbol) → Dec (xs ≡ ys)
≟-list-symbol [] [] = yes refl
≟-list-symbol [] (y ∷ ys) = no (λ ())
≟-list-symbol (x ∷ xs) [] = no (λ ())

≟-list-symbol (x ∷ xs) (y ∷ ys) with ≟-symbol x y | ≟-list-symbol xs ys
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ q → ¬p (inj-symbol q))
  where
  inj-symbol : ∀ {x y : Symbol} {xs ys : List Symbol}
       → x ∷ xs ≡ y ∷ ys
       -----------------
       → x ≡ y
  inj-symbol refl = refl

... | _        | no ¬q    = no (λ q → ¬q (inj-list-symbol q))
  where
  inj-list-symbol : ∀ {x y : Symbol} {xs ys : List Symbol}
       → x ∷ xs ≡ y ∷ ys
       -----------------
       → xs ≡ ys
  inj-list-symbol refl = refl
