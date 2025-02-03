module program-generator.grammar.Grammar where

open import Data.String using (String)
open import Data.Nat using (ℕ)


-- variables are just names
𝕍 : Set
𝕍 = String


-- arithmetic
data 𝔸 : Set where
  const  : ℕ → 𝔸
  var    : 𝕍 → 𝔸
  add    : 𝔸 → 𝔸 → 𝔸    -- A + A
  sub    : 𝔸 → 𝔸 → 𝔸    -- A - A
  mul    : 𝔸 → 𝔸 → 𝔸    -- A × A
  parens : 𝔸 → 𝔸        -- (A)
  

-- boolean
data 𝔹 : Set where
  true   : 𝔹
  false  : 𝔹
  leq    : 𝔸 → 𝔸 → 𝔹    -- A ≤ A
  eq     : 𝔸 → 𝔸 → 𝔹    -- A = A
  not    : 𝔹 → 𝔹        -- !B
  and    : 𝔹 → 𝔹 → 𝔹    -- B && B
  or     : 𝔹 → 𝔹 → 𝔹    -- B || B
  parens : 𝔹 → 𝔹        -- (B)


-- statements
data 𝕊 : Set where
  skip   : 𝕊
  assign : 𝕍 → 𝔸 → 𝕊        -- V ← A (or V ≔ A, haven't decided yet)
  seq    : 𝕊 → 𝕊 → 𝕊        -- S; S
  if     : 𝔹 → 𝕊 → 𝕊 → 𝕊    -- if B then S else S
  while  : 𝔹 → 𝕊 → 𝕊        -- while B do S
  block  : 𝕊 → 𝕊            -- {S}
  
