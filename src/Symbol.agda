module Symbol where

open import Terminal using ( Terminal )
open import NonTerminal using ( NonTerminal )


data Symbol : Set where

  T : Terminal    → Symbol
  N : NonTerminal → Symbol
