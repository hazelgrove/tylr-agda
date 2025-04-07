open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum 
open import Data.Product hiding (zipWith)
open import Data.Maybe hiding (zipWith)
open import Data.List  
open import Data.Nat  
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])

module PBG where

  postulate 
    tile : Set
    sort : Set 
    _≡?_ : (s1 s2 : sort) -> Dec (s1 ≡ s2) 

    s# : sort 
    
    ann-prec : Set 
    _ann≺[_]_ : ann-prec → sort -> ann-prec → Set
    _ann≻[_]_ : ann-prec → sort -> ann-prec → Set

  data pbsymbol : Set where 
    Tile : tile -> pbsymbol 
    Sort : sort -> pbsymbol
  
  data prec : Set where
    Z : prec
    ⊥ : prec
    ⊤ : prec
    P : ann-prec -> prec

  data _≺[_]_ : prec → sort -> prec → Set where

  data _≻[_]_ : prec → sort -> prec → Set where

  data _⪯[_]_ : prec → sort -> prec → Set where
    PLEQ-EQ : ∀{p s} ->
      p ⪯[ s ] p
    PLEQ-LT : ∀{p s q} -> 
      p ≺[ s ] q -> 
      p ⪯[ s ] q

  data _⪰[_]_ : prec → sort -> prec → Set where
    PGEQ-EQ : ∀{p s} ->
      p ⪰[ s ] p
    PGEQ-GT : ∀{p s q} -> 
      p ≻[ s ] q -> 
      p ⪰[ s ] q
  
  data regex : Set where 
    ε : regex
    X : pbsymbol -> regex
    _∣_ : regex -> regex -> regex
    _·_ : regex -> regex -> regex
    _* : regex -> regex
  
  PBG : Set 
  PBG = sort -> prec -> regex

  data _⇒_ : regex -> (List pbsymbol) -> Set where 
    Empty : ε ⇒ []
    Symbol : ∀{x} -> (X x) ⇒ [ x ]
    PlusL : ∀{g1 g2 X} -> 
      g1 ⇒ X -> 
      (g1 ∣ g2) ⇒ X
    PlusR : ∀{g1 g2 X} -> 
      g2 ⇒ X -> 
      (g1 ∣ g2) ⇒ X
    Times : ∀{g1 g2 X Y} -> 
      g1 ⇒ X ->
      g2 ⇒ Y -> 
      (g1 · g2) ⇒ (X ++ Y)
    StarEmpty : ∀{g} -> 
      (g *) ⇒ []
    StarAppend : ∀{g X Y} -> 
      g ⇒ X ->
      (g *) ⇒ Y -> 
      (g *) ⇒ (X ++ Y)