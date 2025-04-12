module Playground where

p₁ : {A B C D : Set} → ((A → B → C) → D) → (A → C) → D
p₁ f g = f λ a b → g a


p₂ : {A B C : Set} → (A → B) → (B → C) → (A → C)
p₂ f g = λ a → g (f a)


p₃ : {A B : Set} → A → (A → B) → B
p₃ f g = g f


p₄ : {A B C : Set} → (A → B → C) → A → B → C
p₄ f a b = f a b


-- associativity of implication

impl-assoc : {A B C : Set}
           → (A → B)
           → (B → C)
           ---------
           → (A → C)

impl-assoc f g a = g (f a)



open import Data.Nat
open import Data.Nat.Properties

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)

add-two : (n : ℕ) → ℕ
add-two n = suc (suc n)

n<n+2 : ∀ (n : ℕ) → n < add-two n
n<n+2 zero    = s≤s z≤n
n<n+2 (suc n) = s≤s (n<n+2 n)

n≤n+2 : ∀ (n : ℕ) → n ≤ add-two n
n≤n+2 zero    = z≤n
n≤n+2 (suc n) = s≤s (n≤n+2 n)

open import Data.Product

n+2-with-prf : (n : ℕ) → Σ[ m ∈ ℕ ] (n < m)
n+2-with-prf n = (add-two n , n<n+2 n)

n+2-with-n+2≡1n+2 : (n : ℕ) → Σ[ m ∈ ℕ ] (m ≡ suc (suc n))
n+2-with-n+2≡1n+2 n = add-two n , refl


open import Data.Nat.DivMod


ex : (m n : ℕ) .⦃ _ : NonZero n ⦄ → m % n ≤ n
ex = m%n≤n

max-3 : (n : ℕ) → ℕ
max-3 n = n % 3

prf : (n : ℕ) → max-3 n ≤ 3
prf zero         = z≤n
prf (suc zero)   = s≤s z≤n
prf (2+ zero)    = s≤s (s≤s z≤n)
prf (2+ (suc n)) = prf n

-- open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩;_∎)

-- to-range : (min max : ℕ) → {{_ : NonZero (max ∸ min)}} → ℕ → ℕ
-- to-range min max x = (x % (max ∸ min)) + min

-- to-range-max : (min max x : ℕ) → {{_ : NonZero (max ∸ min)}} → to-range min max x < max
-- to-range-max min max x = {!!}


-- open import Data.Bool.Base using (T; not)

open Eq using (_≢_)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty

-- open import Data.Irrelevant


-- i : ∀ (a b : ℕ)
--   → 0 < b ∸ a
--   -----------
--   → 0 ≢ b ∸ a

-- i a b 0<b∸a 0≢b∸a = <⇒≢ 0<b∸a 0≢b∸a

-- ii : ∀ {A : Set} {x y : A}
--    → x ≢ y
--    --------
--    → y ≢ x

-- ii x≢y = λ q → x≢y (Eq.sym q)

-- j : ∀ (a b : ℕ)
--   → 0 ≢ b ∸ a
--   -----------
--   → b ∸ a ≢ 0

-- j a b x x₁ = x (Eq.sym x₁)

-- k : ∀ {a b : ℕ}
--   → a ≡ b
--   --------
--   → b ∸ a ≡ 0

-- k {a} {b} a≡b =
--   begin b ∸ a ≡⟨ Eq.cong (λ z → z ∸ a) ((Eq.sym a≡b)) ⟩ n∸n≡0 a

-- kk : ∀ {a b : ℕ}
--   → a ≡ b
--   --------
--   → 0 ≡ b ∸ a

-- kk a≡b = Eq.sym (k a≡b)


<-nonZero : ∀ (a b : ℕ)
          → a < b
          -----------------
          → NonZero (b ∸ a)

<-nonZero a b a<b = ≢-nonZero (λ b∸a≡0 → <⇒≢ (m<n⇒0<n∸m {a} {b} a<b) (Eq.sym b∸a≡0))

-- open import Relation.Binary.Definitions

-- nonZero-< : ∀ (a b : ℕ)
--           → NonZero (b ∸ a)
--           -----------------
--           → a < b

-- nonZero-< a b nz with <-cmp a b
-- ... | tri<  x ¬y ¬z = x
-- ... | tri≈ ¬x  y ¬z = contradiction (k y) (≢-nonZero⁻¹ _ {{nz}})
-- ... | tri> ¬x ¬y  z = {!!}


-- record Range : Set where
--   constructor range

--   field
--     min : ℕ
--     max : ℕ
--     pf  : min < max


-- open Range


-- record InRange : Set where
--   constructor inRange

--   field
--     n    : ℕ
--     rng  : Range
--     prf₁ : rng .min ≤ n
--     prf₂ : n < rng .max


-- to-range′ : (r : Range) → {{_ : NonZero ((r .max) ∸ (r .min))}} → ℕ → ℕ
-- to-range′ (range min max pf) x = (x % (max ∸ min)) + min

-- to-range′-max : (r : Range) → {{nz : NonZero ((r .max) ∸ (r .min))}} (n : ℕ) → to-range′ r n < r .max
-- to-range′-max (range min max pf) {{nz}} n with to-range′ (range min max pf) {{nz}} n
-- ... | g = {!!}


lem₂ : ∀ (x min : ℕ) → min ≤ x + min
lem₂ x min = m≤n+m min x


lem₃ : ∀ (x min max : ℕ) .{{_ : NonZero max}} → min ≤ (x % max) + min
lem₃ x min max = lem₂ (x % max) min


lem₄ : ∀ (x min max : ℕ) .{{_ : NonZero (max ∸ min)}} → x % (max ∸ min) < (max ∸ min)
lem₄ x min max = m%n<n x (max ∸ min)


lem₅ : ∀ (x y z : ℕ)
     → x < y ∸ z
     ------------
     → x < y
     
lem₅ x y z x<y∸z = <-≤-trans x<y∸z (m∸n≤m y z)


lem₆ : ∀ (x min max : ℕ) .{{_ : NonZero (max ∸ min)}}
     → x % (max ∸ min) < (max ∸ min)
     -------------------------------
     → x % (max ∸ min) < max

lem₆ x min max = lem₅ (x % (max ∸ min)) max min


lem₇ : ∀ (x min max : ℕ) .{{_ : NonZero (max ∸ min)}} → x % (max ∸ min) < max
lem₇ x min max = lem₆ x min max (lem₄ x min max)


a+c<b∸c+c⇒a+c<b : ∀ {a b c : ℕ}
     → c ≤ b
     → a + c < (b ∸ c) + c
     ---------------------
     → a + c < b

a+c<b∸c+c⇒a+c<b c≤b prf rewrite m∸n+n≡m c≤b = prf


a<b∸c⇒a+c<b : ∀ {a b c : ℕ}
     → c ≤ b
     → a < (b ∸ c)
     --------------
     → a + c < b

a<b∸c⇒a+c<b {_} {_} {c} c≤b a<b∸c = a+c<b∸c+c⇒a+c<b c≤b (+-monoˡ-< c a<b∸c)


lem₈ : ∀ (x min max : ℕ) .{{_ : NonZero (max ∸ min)}}
     → min ≤ max
     → x % (max ∸ min) < (max ∸ min)
     --------------------------------
     → (x % (max ∸ min)) + min < max

lem₈ x min max min≤max prf = a<b∸c⇒a+c<b {x % (max ∸ min)} {max} {min} min≤max prf


nonzero-m∸n⇒n≤m : ∀ {min max : ℕ} → NonZero (max ∸ min) → min ≤ max
nonzero-m∸n⇒n≤m {zero}    {max}     nz = z≤n
nonzero-m∸n⇒n≤m {suc min} {suc max} nz = s≤s (nonzero-m∸n⇒n≤m nz)


record ℝ (min max : ℕ) : Set where
  constructor 𝕣

  field
    val     : ℕ
    min≤val : min ≤ val
    val<max : val < max


to-ℝange : (min max n : ℕ) → {{nz : NonZero (max ∸ min)}} → ℝ min max
to-ℝange min max x {{nz}} = 𝕣 val min≤val val<max
  where
  val     = (x % (max ∸ min)) + min
  min≤val = lem₃ x min (max ∸ min)
  val<max = lem₈ x min max (nonzero-m∸n⇒n≤m nz) (lem₄ x min max)
