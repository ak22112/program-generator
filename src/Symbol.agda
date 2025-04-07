module Symbol where

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )
open import Data.List using ( List; _∷_; [] )

open import Terminal using ( Terminal )
open import NonTerminal using ( NonTerminal )

-------------------------------------------------------------
-- Symbol type

data Symbol : Set where

  T : Terminal    → Symbol
  N : NonTerminal → Symbol

-------------------------------------------------------------
-- Decidable Equality


-- Decidable equality for Symbol

private
  inj-terminal : ∀ {x y : Terminal}
       → T x ≡ T y
       -----------
       → x ≡ y
  inj-terminal refl = refl

  inj-nonterminal : ∀ {x y : NonTerminal}
       → N x ≡ N y
       -----------
       → x ≡ y
  inj-nonterminal refl = refl

_≟_ : (x y : Symbol) → Dec (x ≡ y)
(T _)  ≟ (N _) = no (λ ())
(N _)  ≟ (T _) = no (λ ())
(T t₁) ≟ (T t₂) with t₁ Terminal.≟ t₂
...                | yes refl = yes refl
...                | no  ¬p   = no (λ q → ¬p (inj-terminal q))
(N n₁) ≟ (N n₂) with n₁ NonTerminal.≟ n₂
...                | yes refl = yes refl
...                | no  ¬p   = no (λ q → ¬p (inj-nonterminal q))


-- Decidable equality for List Symbol

private
  inj-symbol : ∀ {x y : Symbol} {xs ys : List Symbol}
       → x ∷ xs ≡ y ∷ ys
       -----------------
       → x ≡ y
  inj-symbol refl = refl

  inj-list-symbol : ∀ {x y : Symbol} {xs ys : List Symbol}
       → x ∷ xs ≡ y ∷ ys
       -----------------
       → xs ≡ ys
  inj-list-symbol refl = refl

_≟ₗ_ : (xs ys : List Symbol) → Dec (xs ≡ ys)
[]       ≟ₗ []       = yes refl
[]       ≟ₗ (y ∷ ys) = no (λ ())
(x ∷ xs) ≟ₗ []       = no (λ ())
(x ∷ xs) ≟ₗ (y ∷ ys) with x ≟ y | xs ≟ₗ ys
...                 | yes refl | yes refl = yes refl
...                 | no  ¬p   | _        = no (λ q → ¬p (inj-symbol q))
...                 | _        | no  ¬q   = no (λ q → ¬q (inj-list-symbol q))
