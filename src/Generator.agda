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
data ProgramString′ (g : Grammar) : NonTerminal → Set

data StringList     (g : Grammar) : List Symbol → Set
data StringList′    (g : Grammar) : List Symbol → Set

data ProgramString g where

  prod : (i : Fin (length (g .rules)))
       → let r = lookup (g .rules) i in
         (ys : StringList g (r .rhs))
       → ProgramString g (r .lhs)


data ProgramString′ g where

  prod′ : (x : NonTerminal)
        → (xs : List Symbol)
        → (prf : (rule x xs) ∈ (g .rules))
        → (ys : StringList′ g xs)
        → ProgramString′ g x
   

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


data StringList′ g where

  -- empty list
  nil′  : StringList′ g []

  -- list where first element is a non-terminal, followed by a list xs of symbols
  cons′ : {x : NonTerminal}
       → (xs : List Symbol)
       → ProgramString′ g x
       → StringList′ g xs
       → StringList′ g (N x ∷ xs)

  -- list where first element is a terminal, followed by a list xs of symbols
  skip′ : {x : Terminal}
       → (xs : List Symbol)
       → StringList′ g xs
       → StringList′ g (T x ∷ xs)



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


-- get actual string
extract′ : {g : Grammar} {x : NonTerminal} → ProgramString′ g x → String
extract′ = concat ∘ extractStringList
  where
  extractStringList : {g : Grammar} {x : NonTerminal} → ProgramString′ g x → List String
  extractStringList (prod′ _ _ _ ys) = processStringList ys
    where
    extractTerminals : List Symbol → List String
    extractTerminals []         = []
    extractTerminals (T t ∷ xs) = t .name ∷ extractTerminals xs  -- extract terminal symbols
    extractTerminals (N _ ∷ xs) = extractTerminals xs            -- ignore nonterminal

    -- process StringList; extract terminal symbols and expand nonterminals
    processStringList : {g : Grammar} {xs : List Symbol} → StringList′ g xs → List String

    -- empty StringList; return empty list
    processStringList {_} {_}  nil′             = []

    -- skip symbol; extract terminals and continue processing
    processStringList {_} {xs} (skip′ _ rest)   = extractTerminals xs ++ processStringList rest

    -- expand nonterminal; extract terminals, process the nonterminal, and continue
    processStringList {_} {xs} (cons′ _ p rest) = extractTerminals xs ++ extractStringList p ++ processStringList rest



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

open import Data.Product

lookup-with-prf : {A : Set} (xs : List A) (i : Fin (length xs)) → Σ[ x ∈ A ] (x ∈ xs)
lookup-with-prf (x ∷ xs) zero = x , here refl
lookup-with-prf (x ∷ xs) (suc i) with lookup-with-prf xs i
... | fst , snd = fst , there snd


tail′ : {A : Set} → List A → List A
tail′ []       = []      
tail′ (_ ∷ xs) = xs

get-rest-rhs : ℕ → List Symbol
get-rest-rhs n = tail′ ((lookup-rule G (ℕtoFin n (G .rules))) .rhs)

get-rule : ℕ → Rule
get-rule n = lookup-rule G (ℕtoFin n (G .rules))

getRHS : ℕ → List Symbol
getRHS n = (get-rule n) .rhs

rest-rhs : (r : Rule) → List Symbol
rest-rhs r = tail′ (r .rhs)


z : ProgramString′ G (nonTerm "X")
z = prod′ ((xax .proj₁) .lhs) ((xax .proj₁) .rhs) (xax .proj₂) (skip′ (rest-rhs (xax .proj₁))
          (cons′ (rest-rhs (xe .proj₁)) (prod′ (nonTerm "X") ((xe .proj₁) .rhs) (xe .proj₂) nil′) nil′))
  where
  xax : Σ-syntax Rule (λ x → x ∈ G .rules)
  xax = lookup-with-prf (G .rules) zero

  xe : Σ[ r ∈ Rule ] (r ∈ G .rules)
  xe  = lookup-with-prf (G .rules) (suc (suc zero))


record RuleMatch (g : Grammar) (x : NonTerminal) : Set where

  constructor rule-match

  field
    i     : Fin (length (g .rules))
    r     : Rule
    lhs≡x : x ≡ r .lhs
    mem   : r ∈ g .rules

open RuleMatch

open import Relation.Nullary


new-filter : (g : Grammar) (x : NonTerminal) → List (RuleMatch g x)
new-filter g x = go (Data.List.allFin (length (g .rules)))
  where
    go : List (Fin (length (g .rules))) → List (RuleMatch g x)
    go [] = []
    go (i ∷ is) with lookup-with-prf (g .rules) i
    ... | (r , mem) with x NonTerminal.≟ r .lhs
    ... | yes eq = rule-match i r eq mem ∷ go is
    ... | no _   = go is

-- generate : (g : Grammar) (x : NonTerminal) (n : Fin (length (g .rules))) → ProgramString′ g x
-- generate g x n with new-filter g x | lookup-with-prf (g .rules) n
-- ...               | []             | fst , snd = {!!}
-- ...               | i ∷ is         | fst , snd = {!!}


-- mutual
--   generate-stringlist : (g : Grammar) (x : NonTerminal) (rm : RuleMatch g x) → StringList′ g (rm .r .rhs)
--   generate-stringlist g x rm = go (rm .r .rhs)
--     where
--       go : (xs : List Symbol) → StringList′ g xs
--       go []         = nil′
--       go (T t ∷ xs) = skip′ xs (go xs)
--       go (N n ∷ xs) with new-filter g n
--       ... | [] = {!!}
--       ... | rm′ ∷ _ = cons′ xs (generate g n rm′) (go xs)


--   generate : (g : Grammar) (x : NonTerminal) → RuleMatch g x → ProgramString′ g x
--   generate g x rm = Eq.subst (λ lhs → ProgramString′ g lhs) (Eq.sym (rm .lhs≡x))
--     (prod′ (rm .r .lhs) (rm .r .rhs) (rm .mem) (generate-stringlist g x rm))


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
--       rule  = lookup-rule g i
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




-- tail′ : {A : Set} → List A → List A
-- tail′ []       = []      
-- tail′ (_ ∷ xs) = xs

-- get-rest-rhs : ℕ → List Symbol
-- get-rest-rhs n = tail′ ((lookup-rule G (ℕtoFin n (G .rules))) .rhs)

-- get-rule : ℕ → Rule
-- get-rule n = lookup-rule G (ℕtoFin n (G .rules))

-- getRHS : ℕ → List Symbol
-- getRHS n = (get-rule n) .rhs

buildProd : (n : ℕ) → StringList G (getRHS n) → ProgramString G ((get-rule n) .lhs)
buildProd n ys = prod (ℕtoFin n (G .rules)) ys


mutual

  -- temp to check pattern matching
  stringList-test : (g : Grammar) (xs : List Symbol) → StringList g xs
  stringList-test g []         = nil
  stringList-test g (T x ∷ xs) = skip xs (stringList-test g xs)
  stringList-test g (N x ∷ xs) = cons xs {!prod!} (stringList-test g xs)

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


-- Y -> cY -> cd
cd : ProgramString G (nonTerm "Y")
cd = prod (suc (suc (suc zero))) (skip (N (nonTerm "Y") ∷ []) (cons [] (prod (suc (suc (suc (suc zero)))) (skip [] nil)) nil))
