
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

module Term where
  
  mutual 
    data term : Set where 
      _⇒_ : nonteriminal -> (List node) -> term
      
    data node : Set where
      ⌈_⌉ : terminal -> node
      ⌊_⌋ : term -> node

    