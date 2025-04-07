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

  make-triple : {A B C : Set} -> A -> B -> C -> A × B × C 
  make-triple x y z = (x , y , z)

  extend-stack : stack -> (List stack-entry) -> stack 
  extend-stack (τ , l1) l2 = (τ , l2 ++ l1)

  trip-extend-stack : stack -> (List leq) -> (List (Maybe term)) -> (List terminal) -> stack 
  trip-extend-stack 𝕂 xs ys zs = extend-stack 𝕂 (tripZip xs ys zs make-triple)

  walk-entry : Set 
  walk-entry = leq × (Maybe nonteriminal) × terminal

  walk : Set 
  walk = terminal × (List walk-entry)

  wf-walk : walk -> Set
  wf-walk = {!   !}

  walk-of-lists : terminal -> (List leq) -> (List (Maybe nonteriminal)) -> (List terminal) -> walk 
  walk-of-lists = {!   !}

  data push : stack -> (Maybe term) -> terminal -> stack -> Set where
    Shift : ∀{𝕂 𝕊? τₖ 𝕂' τis τs σ?s 𝕊?s ⩿s} -> 
      τs ≡ τₖ ∷ τis ->
      wf-walk (walk-of-lists (hd 𝕂) ⩿s σ?s τs) ->
      𝕂' ≡ trip-extend-stack 𝕂 ⩿s 𝕊?s τs ->
      push 𝕂 𝕊? τₖ 𝕂'

  data parse : stack -> (List terminal) -> stack -> Set where
    ParseNil : ∀{𝕂} -> parse 𝕂 [] 𝕂 
    ParseCons : ∀{𝕋 𝕋s 𝕂 𝕂' 𝕂''} -> 
      push 𝕂 • 𝕋 𝕂' -> 
      parse 𝕂' 𝕋s 𝕂'' -> 
      parse 𝕂 (𝕋 ∷ 𝕋s) 𝕂'