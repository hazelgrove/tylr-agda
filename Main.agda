
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum 
open import Data.Product hiding (zipWith)
open import Data.Maybe hiding (zipWith)
open import Data.List  
open import Data.Nat  
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])

module Main where

  postulate 
    tile : Set
    sort : Set 
    _≡?_ : (s1 s2 : sort) -> Dec (s1 ≡ s2) 

    s# : sort 
    
    ann-precedence : Set 
    _ann≺[_]_ : ann-precedence → sort -> ann-precedence → Set
    _ann≻[_]_ : ann-precedence → sort -> ann-precedence → Set

  data symbol : Set where 
    STile : tile -> symbol 
    SSort : sort -> symbol
  
  data precedence : Set where
    Z : precedence
    ⊥ : precedence
    ⊤ : precedence
    P : ann-precedence -> precedence

  data _≺[_]_ : precedence → sort -> precedence → Set where

  data _≻[_]_ : precedence → sort -> precedence → Set where

  data _⪯[_]_ : precedence → sort -> precedence → Set where
    PLEQ-EQ : ∀{p s} ->
      p ⪯[ s ] p
    PLEQ-LT : ∀{p s q} -> 
      p ≺[ s ] q -> 
      p ⪯[ s ] q

  data _⪰[_]_ : precedence → sort -> precedence → Set where
    PGEQ-EQ : ∀{p s} ->
      p ⪰[ s ] p
    PGEQ-GT : ∀{p s q} -> 
      p ≻[ s ] q -> 
      p ⪰[ s ] q
  
  data regex : Set where 
    ε : regex
    X : symbol -> regex
    _∣_ : regex -> regex -> regex
    _·_ : regex -> regex -> regex
    _* : regex -> regex
  
  PBG : Set 
  PBG = sort -> precedence -> regex

  data grout : Set where 
    〈〉 : sort -> grout
    〈〈 : sort -> grout
    〉〉 : sort -> grout
    〉〈 : sort -> grout

  data terminal : Set where 
    #L : terminal
    #R : terminal
    TTile : tile -> terminal
    TGrout : grout -> terminal

  data nonteriminal : Set where 
    ROOT : nonteriminal
    _⌈_⌉_ : precedence -> sort -> precedence -> nonteriminal

  data cfsymbol : Set where 
    CFT : terminal -> cfsymbol
    CFN : nonteriminal -> cfsymbol
  
  CFG : Set₁
  CFG = nonteriminal -> (List cfsymbol) -> Set


  

  data _⇒_ : regex -> (List symbol) -> Set where 
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

  _〚_〛_[_] : precedence -> symbol -> precedence -> sort -> cfsymbol   
  p 〚 STile t 〛 q [ s ] = CFT (TTile t)
  p 〚 SSort s0 〛 q [ s ] with s0 ≡? s
  p 〚 SSort s0 〛 q [ s ] | yes eq = CFN (p ⌈ s ⌉ q)
  p 〚 SSort s0 〛 q [ s ] | no neq = CFN (⊥ ⌈ s0 ⌉ ⊥)


  bound-bounds-inner : ℕ -> (p : precedence) -> (List precedence) 
  bound-bounds-inner zero p = []
  bound-bounds-inner (suc zero) p = [ p ]
  bound-bounds-inner (2+ n) p = ⊥ ∷ bound-bounds-inner (suc n) p

  bound-bounds : ℕ -> (p : precedence) -> (q : precedence) -> (List precedence) 
  bound-bounds zero p q = []
  bound-bounds (suc n) p q = q ∷ bound-bounds-inner n p

  list-forall : (List Set) -> Set 
  list-forall = foldr (_×_) unit

  tripZip : {A B C D : Set} -> (List A) -> (List B) -> (List C) -> (A -> B -> C -> D) -> (List D)
  tripZip (x ∷ xs) (y ∷ ys) (z ∷ zs) f = f x y z ∷ tripZip xs ys zs f
  tripZip _ _ _ _ = []

  data CFG-of-PBG {G : PBG} : CFG where 
    CPRoot : CFG-of-PBG ROOT ((CFT #L) ∷ ((CFN (⊥ ⌈ s# ⌉ ⊥)) ∷ [ CFT #R ]))
    CPSort : ∀{pL s pR q xs PL PR} ->
      (G s q) ⇒ xs ->
      ((head xs ≡ (just (SSort s))) ->  pL ≺[ s ] q) ->
      ((last xs ≡ (just (SSort s))) ->  q ≻[ s ] pR) ->
      list-forall (zipWith (λ qLi pLi → qLi ⪯[ s ] pLi) (bound-bounds (length xs) pL q) PL) ->
      list-forall (zipWith (λ pRi qRi → pRi ⪰[ s ] qRi) PR (reverse (bound-bounds (length xs) pR q))) ->
      CFG-of-PBG (pL ⌈ s ⌉ pR) (tripZip PL xs PR (λ pLi xi pRi → pLi 〚 xi 〛 pRi [ s ]))

    

    