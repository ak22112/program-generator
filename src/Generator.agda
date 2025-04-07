module Generator where

open import Function.Base using ( _∘_ )
open import Data.List using ( List; _∷_; []; _++_; length )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( here; there )
open import Data.String using ( String; concat )
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )

open import Data.Fin using ( Fin; zero; suc )


open import Terminal
open import NonTerminal
open import Symbol
open import Rule
open import Grammar

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
       → let r = lookup-rule g i in
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
    processStringList {_} {xs} (nil)           = []

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

r₁ : Rule
r₁ = rule (nonTerm "X") (T (term "a") ∷ N (nonTerm "X") ∷ [])

p₁ : ProgramString G (r₁ .lhs)
p₁ = prod zero (skip (N (nonTerm "X") ∷ []) (cons [] (prod (suc (suc zero)) nil) nil))


r₂ : Rule
r₂ = lookup-rule G (suc (suc (suc zero)))

p₂ : ProgramString G (r₂ .lhs)
p₂ = prod (suc (suc (suc zero))) (skip (N (nonTerm "Y") ∷ []) (cons [] (prod (suc (suc (suc (suc zero)))) (skip [] nil)) nil))


r₃ : Rule
r₃ = lookup-rule G (suc (suc (suc (suc zero))))

p₃ : ProgramString G (r₃ .lhs)
p₃ = prod (suc (suc (suc (suc zero)))) (skip [] nil)


-- X → a X → a b Y → a b c Y → a b c d
p₄ : ProgramString G (nonTerm "X")
p₄ = prod zero (skip (N (nonTerm "X") ∷ [])
       (cons [] (prod (suc zero) (skip (N (nonTerm "Y") ∷ [])
         (cons [] (prod ((suc (suc (suc zero)))) (skip (N (nonTerm "Y") ∷ [])
           (cons [] (prod ((suc (suc (suc (suc zero))))) (skip [] nil)) nil))) nil))) nil))
