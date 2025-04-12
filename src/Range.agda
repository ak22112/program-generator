{-# OPTIONS --cubical-compatible --without-K #-}

module Range where

open import Data.Nat using ( ℕ; zero; suc; NonZero; _%_; _+_; _∸_; _≤_; _<_; z≤n; s≤s )
open import Data.Nat.Properties using ( m≤n+m; <-≤-trans; m∸n≤m; m∸n+n≡m; +-monoˡ-< )
open import Data.Nat.DivMod using ( m%n<n )

--------------------------------------------------------------------------

-- This module defines:

  -- Range (type)
  -- clamp (function)

-- They can be found at the bottom of the file

--------------------------------------------------------------------------
-- Helper Proofs

-- In the following proofs, Δ refers to the difference between max and min

private

  min≤mod+min : ∀ {x min max : ℕ} .{{_ : NonZero max}}
       → min ≤ (x % max) + min

  min≤mod+min {x} {min} {max} = m≤n+m min (x % max)


  -- special case of m%n<n where n = x ∸ y, i.e. n is a difference between two other numbers
  x%Δ<Δ : ∀ {x : ℕ} (min : ℕ) {max : ℕ} .{{_ : NonZero (max ∸ min)}}
       → x % (max ∸ min) < (max ∸ min)

  x%Δ<Δ min {max} = m%n<n _ (max ∸ min)


  x<y∸z⇒x<y : ∀ {x y z : ℕ}
            → x < y ∸ z
            ------------
            → x < y

  x<y∸z⇒x<y {_} {y} {z} x<y∸z = <-≤-trans x<y∸z (m∸n≤m y z)


  x%Δ<Δ⇒x%Δ<max : ∀ {x : ℕ} (min : ℕ) {max : ℕ} .{{_ : NonZero (max ∸ min)}}
       → x % (max ∸ min) < (max ∸ min)
       -------------------------------
       → x % (max ∸ min) < max

  x%Δ<Δ⇒x%Δ<max min = x<y∸z⇒x<y {_} {_} {min}


  x%Δ<max : ∀ {x : ℕ} (min : ℕ) {max : ℕ} .{{_ : NonZero (max ∸ min)}}
       → x % (max ∸ min) < max

  x%Δ<max min = x%Δ<Δ⇒x%Δ<max min (x%Δ<Δ min)


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


  x%Δ<Δ⇒x%Δ+min<max : ∀ {x : ℕ} (min : ℕ) {max : ℕ} .{{_ : NonZero (max ∸ min)}}
       → min ≤ max
       → x % (max ∸ min) < (max ∸ min)
       --------------------------------
       → (x % (max ∸ min)) + min < max

  x%Δ<Δ⇒x%Δ+min<max min min≤max prf = a<b∸c⇒a+c<b min≤max prf


  min≤max : ∀ {min max : ℕ} .{{_ : NonZero (max ∸ min)}}
                  → min ≤ max

  min≤max {zero}  {_}     = z≤n
  min≤max {suc _} {suc _} = s≤s min≤max


  x%Δ+min<max : ∀ {x : ℕ} (min : ℕ) {max : ℕ} .{{_ : NonZero (max ∸ min)}}
       → (x % (max ∸ min)) + min < max

  x%Δ+min<max min = x%Δ<Δ⇒x%Δ+min<max min min≤max (x%Δ<Δ min)


record Range (min max : ℕ) .{{_ : NonZero (max ∸ min)}} : Set where
  constructor range

  field
    val     : ℕ
    min≤val : min ≤ val
    val<max : val < max


-- clamps x between min and max
-- returns a Range record, containing the clamped value, and proofs that it is in the range
clamp : (min max x : ℕ) .{{_ : NonZero (max ∸ min)}} → Range min max
clamp min max x = range val min≤val val<max
  where
  val     = (x % (max ∸ min)) + min
  min≤val = min≤mod+min
  val<max = x%Δ+min<max min
