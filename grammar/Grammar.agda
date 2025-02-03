module program-generator.grammar.Grammar where

open import Data.String using (String)
open import Data.Nat using (ℕ)


-- variables are just names
𝕍 : Set
𝕍 = String


-- arithmetic
data 𝔸 : Set where
  Const  : ℕ → 𝔸
  Var    : 𝕍 → 𝔸
  Add    : 𝔸 → 𝔸 → 𝔸    -- A + A
  Sub    : 𝔸 → 𝔸 → 𝔸    -- A - A
  Mul    : 𝔸 → 𝔸 → 𝔸    -- A × A
  Parens : 𝔸 → 𝔸        -- (A)
  

-- boolean
data 𝔹 : Set where
  True   : 𝔹
  False  : 𝔹
  Leq    : 𝔸 → 𝔸 → 𝔹    -- A ≤ A
  Eq     : 𝔸 → 𝔸 → 𝔹    -- A = A
  Not    : 𝔹 → 𝔹        -- !B
  And    : 𝔹 → 𝔹 → 𝔹    -- B && B
  Or     : 𝔹 → 𝔹 → 𝔹    -- B || B
  Parens : 𝔹 → 𝔹        -- (B)


-- statements
data 𝕊 : Set where
  Skip   : 𝕊
  Assign : 𝕍 → 𝔸 → 𝕊        -- V ← A (or V ≔ A)
  Seq    : 𝕊 → 𝕊 → 𝕊        -- S; S
  If     : 𝔹 → 𝕊 → 𝕊 → 𝕊    -- if B then S else S
  While  : 𝔹 → 𝕊 → 𝕊        -- while B do S
  Block  : 𝕊 → 𝕊            -- {S}
  
