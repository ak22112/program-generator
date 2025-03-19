module Generator where

open import Agda.Builtin.String

open import Function.Base using ( _∘_ )

open import Data.List using ( List; _∷_; []; _++_ )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( here; there )

-- beware potential conflicts in future???
import Data.String.Base as String

import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_; refl; cong )


open import Terminal
open import NonTerminal
open import Symbol
open import Rule
open import Grammar

-- open records to make dot notation accessible
open Terminal.Terminal
open NonTerminal.NonTerminal
open Rule.Rule
open Grammar.Grammar


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
  extractStringList (prod _ ys _) = processStringList ys
    where
    extractTerminals : List Symbol → List String
    extractTerminals []         = []
    extractTerminals (T t ∷ xs) = t .name ∷ extractTerminals xs  -- extract terminal symbols
    extractTerminals (N _ ∷ xs) = extractTerminals xs            -- ignore nonterminal

    -- process StringList; extract terminal symbols and expand nonterminals
    processStringList : {g : Grammar} {xs : List Symbol} → StringList g xs → List String

    -- empty StringList; return empty list
    processStringList {g} {xs} (nil)           = []

    -- skip symbol; extract terminals and continue processing
    processStringList {g} {xs} (skip _ rest)   = extractTerminals xs ++ processStringList rest

    -- expand nonterminal; extract terminals, process the nonterminal, and continue
    processStringList {g} {xs} (cons _ p rest) = extractTerminals xs ++ extractStringList p ++ processStringList rest



open import Relation.Nullary
open import Data.String.Properties

decEqNonTerminal : (x y : NonTerminal) → Dec (x ≡ y)
decEqNonTerminal (nonTerm name₁) (nonTerm name₂) with name₁ ≟ name₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (cong NonTerminal.name q))


decEqTerminal : (x y : Terminal) → Dec (x ≡ y)
decEqTerminal (term name₁) (term name₂) with name₁ ≟ name₂
... | yes refl = yes refl
... | no ¬p    = no λ q → ¬p (cong Terminal.name q)



decEqSymbol : (x y : Symbol) → Dec (x ≡ y)
decEqSymbol (T t₁) (T t₂) with decEqTerminal t₁ t₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (inj-terminal q))
  where
  inj-terminal : ∀ {x y : Terminal}
       → T x ≡ T y
       -----------
       → x ≡ y
  inj-terminal refl = refl

decEqSymbol (N n₁) (N n₂) with decEqNonTerminal n₁ n₂
... | yes refl = yes refl
... | no ¬p    = no (λ q → ¬p (inj-nonterminal q))
  where
  inj-nonterminal : ∀ {x y : NonTerminal}
       → N x ≡ N y
       -----------
       → x ≡ y
  inj-nonterminal refl = refl

decEqSymbol (T _) (N _) = no (λ ())
decEqSymbol (N _) (T _) = no (λ ())


decEqListSymbol : (xs ys : List Symbol) → Dec (xs ≡ ys)
decEqListSymbol [] [] = yes refl
decEqListSymbol [] (y ∷ ys) = no (λ ())
decEqListSymbol (x ∷ xs) [] = no (λ ())
decEqListSymbol (x ∷ xs) (y ∷ ys) with decEqSymbol x y | decEqListSymbol xs ys
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


decEqRule : (r₁ r₂ : Rule) → Dec (r₁ ≡ r₂)
decEqRule (rule lhs₁ rhs₁) (rule lhs₂ rhs₂)
  with decEqNonTerminal lhs₁ lhs₂ | decEqListSymbol rhs₁ rhs₂
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no (λ q → ¬p (cong Rule.lhs q))
... | _        | no ¬q    = no (λ q → ¬q (cong Rule.rhs q))



open import Data.List.Base using ( filter )

-- filter Grammar by non-terminal
-- see list filtering functions here https://agda.github.io/agda-stdlib/v2.1/Data.List.Base.html
filterGrammar : (g : Grammar) (x : NonTerminal) → Grammar
filterGrammar g x = grammar (filter (λ r → decEqNonTerminal (r .lhs) x) (g .rules))


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
