module Generator where

open import Types
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Bool

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)


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
data ProgramString′ (g : Grammar) : NonTerminal → Set
data StringList     (g : Grammar) : List Symbol → Set



data ProgramString g where

  prod : (r : Rule)
       → (ys : StringList g (r .rhs))
       → (prf : InGrammar g r)
       → ProgramString g (r .lhs)



data ProgramString′ g where

  prod′ : (x : NonTerminal)
        → (xs : List Symbol)
        → (ys : StringList g xs)
        → (prf : InGrammar′ g x xs)
        → ProgramString′ g x




data StringList g where

  nil  : StringList g []
  
  cons : {x : NonTerminal}
       → (xs : List Symbol)
       → ProgramString g x
       → StringList g xs
       → StringList g (N x ∷ xs)
       
  skip : {x : Terminal}
       → (xs : List Symbol)
       → StringList g xs
       → StringList g (T x ∷ xs)



-- haven't actually checked what this does; just used auto solver, seems to be ok
extract : {g : Grammar} {x : NonTerminal} → ProgramString g x → String
extract (prod r ys prf) = r .lhs .name




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

  

-- produce a program string (C-c C-a will fill the hole)
p₁ : ProgramString G (r₁ .lhs)
p₁ = prod r₁ {!!} (here refl)

-- another program string will hole filled in
p₂ : ProgramString G (r₂ .lhs)
p₂ = prod r₂ (skip (N (nonTerm "Y") ∷ [])
               (cons []
                (prod (rule (nonTerm "Y") (T (term "d") ∷ [])) (skip [] nil)
                 (there (there (there (there (here refl))))))
                nil)) (there (there (there (here refl))))
