module Generator where

open import Types
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Bool

open import Function.Base using ( _∘_ )

open import Data.List using ( List; _∷_; []; _++_ )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( here; there )

-- beware potential conflicts in future???
import Data.String.Base as String

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl )


open Terminal
open NonTerminal
open Rule
open Grammar


-- check rule directly
InGrammar : Grammar → Rule → Set
InGrammar g r = r ∈ g .rules

-- pass in lhs and rhs separately
InGrammar′ : Grammar → NonTerminal → List Symbol → Set
InGrammar′ g x xs = InGrammar g (rule x xs)



-- forward declaration (this is to allow mutual recursive functions)
data ProgramString  (g : Grammar) : NonTerminal → Set
data StringList     (g : Grammar) : List Symbol → Set



data ProgramString g where

  prod : (r : Rule)
       → (ys : StringList g (r .rhs))
       → (prf : InGrammar g r)
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
extract = String.concat ∘ extractStringList
  where
  extractStringList : {g : Grammar} {x : NonTerminal} → ProgramString g x → List String
  extractStringList (prod r ys prf) = processStringList ys
    where
    extractTerminals : List Symbol → List String
    extractTerminals []         = []
    extractTerminals (T t ∷ xs) = t .name ∷ extractTerminals xs  -- extract terminal symbols
    extractTerminals (N _ ∷ xs) = extractTerminals xs            -- ignore nonterminal

    -- process StringList; extract terminal symbols and expand nonterminals
    processStringList : {g : Grammar} {xs : List Symbol} → StringList g xs → List String

    -- empty StringList; return empty list
    processStringList {g} {xs} (nil)             = []

    -- skip symbol; extract terminals and continue processing (can only use xs)
    processStringList {g} {xs} (skip rhs rest)   = extractTerminals xs ++ processStringList rest

    -- expand nonterminal; extract terminals, process the nonterminal, and continue (can use xs or rhs)
    processStringList {g} {xs} (cons rhs p rest) = extractTerminals xs ++ extractStringList p ++ processStringList rest




-- concrete examples

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



-- rules and proofs they are in the grammar
r₁ : Rule
r₁ = rule (nonTerm "X") (T (term "a") ∷ N (nonTerm "X") ∷ [])

prf₁ : InGrammar G r₁
prf₁ = here refl


r₂ : Rule
r₂ = rule (nonTerm "Y") (T (term "c") ∷ N (nonTerm "Y") ∷ [])

prf₂ : InGrammar G r₂
prf₂ = there (there (there (here refl)))


r₃ : Rule
r₃ = rule (nonTerm "Y") (T (term "d") ∷ []) 

-- produce a program string (X → a X → a ϵ → a)
p₁ : ProgramString G (r₁ .lhs)
p₁ = prod r₁ (skip (N (nonTerm "X") ∷ [])
               (cons []
                (prod (rule (nonTerm "X") []) nil (there (there (here refl))))
                nil)) (here refl)

-- another program string (Y → c Y → c d)
p₂ : ProgramString G (r₂ .lhs)
p₂ = prod r₂ (skip (N (nonTerm "Y") ∷ [])
               (cons []
                (prod (rule (nonTerm "Y") (T (term "d") ∷ [])) (skip [] nil)
                 (there (there (there (there (here refl))))))
                nil)) (there (there (there (here refl))))


-- another program string (Y → d)
p₃ : ProgramString G (r₃ .lhs)
p₃ = prod r₃ (skip [] nil) (there (there (there (there (here refl)))))
