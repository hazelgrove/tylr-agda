
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum hiding (map)
open import Data.Product hiding (zipWith; map)
open import Data.Maybe hiding (zipWith; map)
-- open import Data.List 
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

  data chain-extension (A : Set) : Set where 
    ∙ : chain-extension A
    _∷_[_]_ : chain-extension A -> leq -> (Maybe A) -> terminal -> chain-extension A

  chain : (A : Set) -> Set 
  chain A = terminal × chain-extension A
  
  hd : ∀ {A} -> chain A -> terminal 
  hd (τ , ∙) = τ
  hd (_ , _ ∷ _ [ _ ] τ) = τ

  hd-ext : ∀ {A} -> chain-extension A -> Maybe terminal 
  hd-ext ∙ = nothing
  hd-ext (_ ∷ _ [ _ ] τ) = just τ

  concat-chain-extension : ∀ {A} -> chain-extension A -> chain-extension A -> chain-extension A
  concat-chain-extension 𝕂1 ∙ = 𝕂1
  concat-chain-extension 𝕂1 (𝕂2 ∷ ⩿ [ A? ] τ) = (concat-chain-extension 𝕂1 𝕂2) ∷ ⩿ [ A? ] τ

  extend-chain : ∀ {A} -> chain A -> chain-extension A -> chain A
  extend-chain (τ , 𝕂1) 𝕂2 = τ , (concat-chain-extension 𝕂1 𝕂2)

  stack : Set 
  stack = chain term

  stack-extension : Set 
  stack-extension = chain-extension term

  walk : Set 
  walk = chain nonteriminal

  walk-extension : Set 
  walk-extension = chain-extension nonteriminal

  data terrace {A} : chain-extension A -> Set where 
    TNil : ∀ {A? τ} -> terrace (∙ ∷ ⋖ [ A? ] τ) 
    TCons : ∀ {𝕂 ⩿ A? τ A?' τ'} -> 
      terrace (𝕂 ∷ ⩿ [ A? ] τ) ->
      terrace ((𝕂 ∷ ⩿ [ A? ] τ) ∷ ≐ [ A?' ] τ')