
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum hiding (map)
open import Data.Product hiding (zipWith; map)
open import Data.Maybe hiding (zipWith; map)
open import Data.List 
open import Data.Nat  
open import Relation.Nullary hiding (⌊_⌋)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import PBG
open import CFG
open import GG
open import Term

module Stack where

  data leq : Set where
    ⋖ : leq
    ≐ : leq

  data comparison : Set where
    CLeq : leq -> comparison
    ⋗ : comparison

  -- data stack : Set where 
  --   · : terminal -> stack
  --   _∷_[_]_ : stack -> leq -> (Maybe term) -> terminal -> stack

  -- hd : stack -> terminal 
  -- hd (· τ) = τ
  -- hd (𝕂 ∷ ⩿ [ 𝕊? ] τ) = τ

  stack-entry : Set 
  stack-entry = leq × (Maybe term) × terminal

  -- the head of the list is the (right) face of the stack
  stack : Set
  stack = terminal × (List stack-entry)

  hd : stack -> terminal 
  hd (τ , []) = τ
  hd (_ , (⩿ , 𝕊? , τ) ∷ _) = τ
  

  