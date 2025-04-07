open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum hiding (map)
open import Data.Product hiding (zipWith; map)
open import Data.Maybe renaming (nothing to •) hiding (zipWith; map) 
open import Data.List 
open import Data.Nat  
open import Relation.Nullary hiding (⌊_⌋)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import PBG
open import CFG
open import GG
open import Term
open import Stack

module Parse where
  
  wf-walk : walk -> Set
  wf-walk = {!   !}

  fill-walk-extension : (Maybe term) -> walk-extension -> stack-extension -> Set 
  fill-walk-extension = {!   !}

  data push : stack -> (Maybe term) -> terminal -> stack -> Set where
    Shift : ∀{𝕂 𝕊? τₖ 𝕎+ 𝕂+ 𝕂'} -> 
      hd-ext 𝕎+ ≡ just τₖ ->
      wf-walk (hd 𝕂 , 𝕎+) ->
      fill-walk-extension 𝕊? 𝕎+ 𝕂+ ->
      𝕂' ≡ extend-chain 𝕂 𝕂+ ->
      push 𝕂 𝕊? τₖ 𝕂'
    Reduce : 
      push 𝕂₀ 𝕊?' τ 𝕂' ->
      push 𝕂 𝕊? τ 𝕂'


  data parse : stack -> (List terminal) -> stack -> Set where
    ParseNil : ∀{𝕂} -> parse 𝕂 [] 𝕂 
    ParseCons : ∀{𝕋 𝕋s 𝕂 𝕂' 𝕂''} -> 
      push 𝕂 • 𝕋 𝕂' -> 
      parse 𝕂' 𝕋s 𝕂'' -> 
      parse 𝕂 (𝕋 ∷ 𝕋s) 𝕂'