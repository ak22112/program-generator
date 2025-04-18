{-# OPTIONS --sized-types #-}

module Generator where

open import Function.Base using ( _∘_; case_of_ )
open import Data.Nat.Base using ( NonZero; ℕ; zero; suc )
open import Data.List using ( List; _∷_; []; _++_; length; lookup )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( here; there )
open import Data.String using ( String; concat )
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

open import Data.Fin using ( Fin; zero; suc )

open import Data.Maybe


open import Terminal
open import NonTerminal
open import Symbol
open import Rule
open import Grammar
open import Random

-- open records to make dot notation accessible
open Terminal.Terminal        -- .name
open NonTerminal.NonTerminal  -- .name
open Rule.Rule                -- .lhs; .rhs
open Grammar.Grammar          -- .rules


-- forward declaration (this is to allow mutual recursive functions)
data ProgramString  (g : Grammar) : NonTerminal → Set
data StringList     (g : Grammar) : List Symbol → Set


data ProgramString g where

  prod : (i : Fin (length (g .rules)))
       → let r = lookup (g .rules) i in
         (ys : StringList g (r .rhs))
       → ProgramString g (r .lhs)
   

data StringList g where

  -- empty list
  nil  : StringList g []

  -- list where first element is a non-terminal, followed by a list xs of symbols
  cons : {x : NonTerminal}
       → (xs : List Symbol)
       → ProgramString g x
       → StringList g xs
       → StringList g (N x ∷ xs)

  -- list where first element is a terminal, followed by a list xs of symbols
  skip : {x : Terminal}
       → (xs : List Symbol)
       → StringList g xs
       → StringList g (T x ∷ xs)



-- get actual string
extract : {g : Grammar} {x : NonTerminal} → ProgramString g x → String
extract = concat ∘ extractStringList
  where
  extractStringList : {g : Grammar} {x : NonTerminal} → ProgramString g x → List String
  extractStringList (prod _ ys) = processStringList ys
    where
    extractTerminals : List Symbol → List String
    extractTerminals []         = []
    extractTerminals (T t ∷ xs) = t .name ∷ extractTerminals xs  -- extract terminal symbols
    extractTerminals (N _ ∷ xs) = extractTerminals xs            -- ignore nonterminal

    -- process StringList; extract terminal symbols and expand nonterminals
    processStringList : {g : Grammar} {xs : List Symbol} → StringList g xs → List String

    -- empty StringList; return empty list
    processStringList {_} {_}  nil             = []

    -- skip symbol; extract terminals and continue processing
    processStringList {_} {xs} (skip _ rest)   = extractTerminals xs ++ processStringList rest

    -- expand nonterminal; extract terminals, process the nonterminal, and continue
    processStringList {_} {xs} (cons _ p rest) = extractTerminals xs ++ extractStringList p ++ processStringList rest


-- concrete examples --

-- grammar
G : Grammar
G = grammar
    (
      rule (nonTerm "X") (T (term "a") ∷ N (nonTerm "X") ∷ []) ∷    -- X → a X
      rule (nonTerm "X") (T (term "b") ∷ N (nonTerm "Y") ∷ []) ∷    -- X → b Y
      rule (nonTerm "X") []                                    ∷    -- X → ϵ
      rule (nonTerm "Y") (T (term "c") ∷ N (nonTerm "Y") ∷ []) ∷    -- Y → c Y
      rule (nonTerm "Y") (T (term "d") ∷ [])                   ∷    -- Y → d
      []
    )


-- rules and programs

p₁ : ProgramString G (nonTerm "X")
p₁ = prod zero (skip (N (nonTerm "X") ∷ []) (cons [] (prod (suc (suc zero)) nil) nil))

p₁′ : ProgramString G (nonTerm "X")
p₁′ = prod (ℕtoFin 0 (G .rules)) (skip (getrhs 0) (cons (getrhs 2) (prod (ℕtoFin 2 ((G .rules))) nil) nil))
  where
  getrhs : ℕ → List Symbol
  getrhs n = tail ((lookup-rule G (ℕtoFin n (G .rules))) .rhs)
    where
    tail : {A : Set} → List A → List A
    tail []       = []      
    tail (_ ∷ xs) = xs
    

r₂ : Rule
r₂ = lookup-rule G (suc (suc (suc zero)))


p₂ : ProgramString G (r₂ .lhs)
p₂ = prod (suc (suc (suc zero))) (skip (N (nonTerm "Y") ∷ []) (cons [] (prod (suc (suc (suc (suc zero)))) (skip [] nil)) nil))


r₃ : Rule
r₃ = lookup-rule G (suc (suc (suc (suc zero))))

p₃ : ProgramString G (r₃ .lhs)
p₃ = prod (ℕtoFin 4 (G .rules)) (skip [] nil)


-- X → a X → a b Y → a b c Y → a b c d
p₄ : ProgramString G (nonTerm "X")
p₄ = prod zero (skip (N (nonTerm "X") ∷ [])
       (cons [] (prod (suc zero) (skip (N (nonTerm "Y") ∷ [])
         (cons [] (prod ((suc (suc (suc zero)))) (skip (N (nonTerm "Y") ∷ [])
           (cons [] (prod ((suc (suc (suc (suc zero))))) (skip [] nil)) nil))) nil))) nil))

-- X → a X → a b Y → a b c Y → a b c d
p₅ : ProgramString G (nonTerm "X")
p₅ = prod (ℕtoFin 0 (G .rules)) (skip (N (nonTerm "X") ∷ [])
       (cons [] (prod ((ℕtoFin 1 (G .rules))) (skip (N (nonTerm "Y") ∷ [])
         (cons [] (prod (ℕtoFin 3 (G .rules)) (skip (N (nonTerm "Y") ∷ [])
           (cons [] (prod (ℕtoFin 4 (G .rules)) (skip [] nil)) nil))) nil))) nil))


-- might not need this to be a Maybe
-- when pattern matching on a stringList, should only need to call this on the `cons` case
-- also might need to move this to the Grammar module
lookup-valid-rule : (g : Grammar) (x : NonTerminal) → Maybe Rule
lookup-valid-rule g x with filter-grammar-index g x
...        | []     = nothing
...        | i ∷ is = just (lookup-rule g (lookup-in-bounds (i ∷ is) rand))
  where
  rand : ℕ
  rand = 0 -- TODO: pick randomly


open import Codata.Sized.Stream as Stream using ( Stream; head; tail )
open import Data.Product

open import Relation.Nullary

-- generate : (g : Grammar) (x : NonTerminal) (seed : ℕ) → Maybe (ProgramString g x)
-- generate g x seed = generate-helper g x (randoms seed)
--   where
--   generate-helper : (g : Grammar) (x : NonTerminal) (stream : Stream ℕ _) → Maybe (ProgramString g x)
--   generate-helper g x stream with filter-grammar-index g x
--   ... | []     = nothing
--   ... | i ∷ is = let
--       rand  = head stream
--       index = ℕtoFin rand (i ∷ is)
--       rule  = lookup-rule g {!!}
--     in
--       {!!}


-- mutual

--   maybeStringList : (g : Grammar) → ℕ → (ys : List Symbol) → Maybe (StringList g ys)
--   maybeStringList g fuel []               = just nil
--   maybeStringList g fuel (T t ∷ ys)       = do rest ← maybeStringList g fuel ys ; just (skip ys rest)
--   maybeStringList g (suc fuel) (N n ∷ ys) = do p ← generate g n ; rest ← maybeStringList g fuel ys ; just (cons ys p rest)
--   maybeStringList g zero _                = nothing


--   generate : (g : Grammar) (x : NonTerminal) → Maybe (ProgramString g x)
--   generate g x with filter-grammar-index g x
--   ... | []    = nothing
--   ... | i ∷ _ with lookup-rule g i
--   ...            | rule lhs rhs = maybeStringList g rhs >>= λ ys → just {!!}




tail′ : {A : Set} → List A → List A
tail′ []       = []      
tail′ (_ ∷ xs) = xs

get-rest-rhs : ℕ → List Symbol
get-rest-rhs n = tail′ ((lookup-rule G (ℕtoFin n (G .rules))) .rhs)

get-rule : ℕ → Rule
get-rule n = lookup-rule G (ℕtoFin n (G .rules))

getRHS : ℕ → List Symbol
getRHS n = (get-rule n) .rhs

buildProd : (n : ℕ) → StringList G (getRHS n) → ProgramString G ((get-rule n) .lhs)
buildProd n ys = prod (ℕtoFin n (G .rules)) ys


mutual

  -- temp to check pattern matching
  stringList-test : (g : Grammar) (xs : List Symbol) → StringList g xs
  stringList-test g []         = nil
  stringList-test g (T x ∷ xs) = skip xs (stringList-test g xs)
  stringList-test g (N x ∷ xs) = cons xs {!!} (stringList-test g xs)

  helper : {g : Grammar} (xs : List Symbol) (stream : Stream ℕ _) → StringList g xs
  helper []        stream = nil
  helper (x ∷ xs)  stream with x
  ... | T x₁ = skip xs (helper xs (tail stream))
  ... | N x₁ = cons xs {!!} (helper xs (tail stream))

  generate : (g : Grammar) (stream : Stream ℕ _) .{{_ : NonZero (length (g .rules))}} → ProgramString g ((lookup (g .rules) (ℕtoFin (head stream) (g .rules))) .lhs)
  generate g stream using (idx , r , rhs) ← let idx = ℕtoFin (head stream) (g .rules) in idx
                                          , let r   = lookup (g .rules) idx in r
                                          , let rhs = r .rhs in rhs

                    with filter-grammar-index g (r .lhs)
  ... | []     = {!!} -- don't know how to handle this. Maybe?
  ... | i ∷ is = {!!} -- could just match is (no ∷)
